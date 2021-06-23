# Recursive reference &emsp; [![Latest Version]][crates.io] [![Docs version]][docs]

[Latest Version]: https://img.shields.io/crates/v/recursive_reference.svg
[crates.io]: https://crates.io/crates/recursive_reference
[Docs version]: https://docs.rs/recursive_reference/badge.svg
[docs]: https://docs.rs/recursive_reference/

This crate provides a way to traverse recursive structures easily and safely.
Rust's lifetime rules will usually force you to either only walk forward through the structure,
or use recursion, calling your method recursively every time you go down a node,
and returning every time you want to go back up, which leads to terrible code.

Instead, you can use the [`RecRef`] type, to safely and dynamically walk up
and down your recursive structure.

[documentation](https://docs.rs/recursive_reference)
[crates.io](https://crates.io/crates/recursive_reference)
[repository](https://github.com/noamtashma/recursive_reference)

# Examples

 Say we have a recursive linked list structure
 ----------------------------------------------
```rust
enum List<T> {
    Root(Box<Node<T>>),
    Empty,
}
struct Node<T> {
    value: T,
    next: List<T>,
}
```

 We can use a [`RecRef`] directly
 ----------------------------------------------
```rust
use recursive_reference::*;

fn main() -> Result<(), ()> {
    // crate a list to test
    let node1 = Node {
        value: 5,
        next: List::Empty,
    };
    let mut node2 = Node {
        value: 2,
        next: List::Root(Box::new(node1)),
    };

    // create a `RecRef`
    let mut rec_ref = RecRef::new(&mut node2);
    // rec_ref is a smart pointer to the current node
    assert_eq!(rec_ref.value, 2);

    // move forward through the list
    RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
        List::Root(next_node) => Ok(next_node),
        List::Empty => Err(()),
    })?;
    assert_eq!(rec_ref.value, 5); // now we're at the second node

    // pop the `RecRef`, moving it back to the head
    RecRef::pop(&mut rec_ref).ok_or(())?;
    assert_eq!(rec_ref.value, 2);
    Ok(())
}
```

 We can also wrap a [`RecRef`] in a walker struct
 ----------------------------------------------
```rust
use recursive_reference::*;
struct Walker<'a, T> {
    rec_ref: RecRef<'a, Node<T>>,
}
impl<'a, T> Walker<'a, T> {
    /// Crates a new Walker
    pub fn new(node: &'a mut Node<T>) -> Self {
        Walker {
            rec_ref: RecRef::new(node),
        }
    }

    /// Returns `None` when at the tail end of the list.
    /// Moves to the next node.
    pub fn next(&mut self) -> Option<()> {
        RecRef::extend_result(&mut self.rec_ref, |current| match &mut current.next {
            List::Empty => Err(()),
            List::Root(node) => Ok(node),
        })
        .ok()
    }

    /// Returns `None` when at the head of the list.
    /// Goes back to the previous node.
    pub fn prev(&mut self) -> Option<()> {
        RecRef::pop(&mut self.rec_ref)?;
        Some(())
    }

    /// Returns `None` when at the tail end of the list.
    /// Returns `Some(reference)` where `reference` is a mutqable reference to the current value.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.rec_ref.value
    }
}

fn main() -> Result<(), ()> {
    // crate a list to test
    let node1 = Node {
        value: 5,
        next: List::Empty,
    };
    let mut node2 = Node {
        value: 2,
        next: List::Root(Box::new(node1)),
    };

    // create a walker for the list
    let mut walker = Walker::new(&mut node2);
    // walker has mutable access to the node value
    assert_eq!(*walker.value_mut(), 2);
    // move to the next node
    walker.next().ok_or(())?;
    assert_eq!(*walker.value_mut(), 5);
    assert_eq!(walker.next(), None); // currently at the end of the list
                                     // move back
    walker.prev().ok_or(())?;
    assert_eq!(*walker.value_mut(), 2);
    Ok(())
}
```
 With a [`RecRef`] you can
 ----------------------------------------------
 * Use the current reference (i.e, the top reference).
  the [`RecRef`] is a smart pointer to it.
 * Freeze the current reference
  and extend the [`RecRef`] with a new reference derived from it, using [`extend`] and similar functions.
  for example, push to the stack a reference to the child of the current node.
 * Pop the stack to get back to the previous reference, unfreezing it.
 


 # Alternative Comparison
 There are many alternatives to using [`RecRef`]. They all have their upsides and downsides.
 We only compare them to `RecRef`, so we only list the downsides that `RecRef` solves.
 Many of these alternatives can be better, depending on the usecase. Here are they, roughly from the basic to the sophisticated:
 * Plain recursive data structures. They require writing recursive functions where the recursion matches exactly with your access pattern. Anything but the most basic functions are very hard to write this way.
 * Pointer-based data structures can be efficient and convenient, but unsafe.
 * `Rc` and `RefCell` based data structures can be convenient, but require overhead to store metadata and check it. They also make ownership bugs surface at runtime rather than compile time. (You might want to look at `static-rc`, which is a crate that can improve this).
 * Slab-based. That is, store all of your nodes in some kind of collection, and have the links be
   indices into the collection.
   * Requires your pointers to go through an extra indirection.
   * Your structure will be tied to the slab (you can't split parts of it and send them to another owner)
   * If you give a borrow to the structure, the whole structure could be changed.
 * Arena-based recursive data structures. That is, an arena is like a slab, that can't delete its elements, and can therefore give long-lasting references to its elements.
   * The nodes can't be freed until the whole structure is freed.
   * Your structure will be tied to the arena (you can't split parts of it and send them to another owner)
 * There are also alternative cells in the `qcell` crate and the `ghost-cell` crate, and maybe even more
   Interesting options.
 
 # [`RecRef`] Pros
 * [`RecRef`] can be used with any existing data structure, including any data structure
   that is not written by you. [`RecRef`] can work with plain structures, `Rc`/`RefCell` based structures, arena based structures, and so on. Although, working with plain structures is recommended.
 * [`RecRef`] incurs no space overhead to the structure.
 * [`RecRef`] is safe and doesn't panic.
 * [`RecRef`] does not tie it down, i.e, prevent you from splitting the structure's ownership.

 # [`RecRef`] Cons
 * [`RecRef`] only allows you to modify your structure at a single point at a time.
 * The [`RecRef`] itself requires a space overhead the size of your path in the recursive structure when 
   traversing it. It also takes some time to pop and push elements to the vector.
   This is the same overhead that is needed in every structure that doesn't have parent pointers.
 * The [`RecRef`] is overall efficient, but internally pushes elements to a vector.
   
 
 
 
 # Minor details
 * All code is tested with a real-world library under miri.
 * Since version "0.3.0", the library requires rust version 1.53 to compile correctly. If it is not present, use version "0.2.0".
 * Internally, [`RecRef`] pushes and pops elements from a vector. That means that the library
   requires an allocator to be present. In addition, it means that you might have latency problems if you're using a very large [`RecRef`].
   This can be theoretically solved by switching the [`RecRef`] to a low-latency stack.


 # Safety
 The [`RecRef`] type is implemented using unsafe rust, but provides a safe interface.
 The [`RecRef`]'s methods' types guarantee that the references will always have a legal lifetime
 and will respect rust's borrow rules, even if that lifetime is not known in advance.

 The [`RecRef`] obeys rust's borrowing rules, by simulating freezing. Whenever
 you extend a [`RecRef`] with a reference `child_ref` that is derived from the current
 reference `parent_ref`, the [`RecRef`] freezes `parent_ref`, and no longer allows
 `parent_ref` to be used.
 When `child_ref` will be popped from the [`RecRef`],
 `parent_ref` will be allowed to be used again.

 This is essentially the same as what would have happened if you wrote your functions recursively,
 but it's decoupled from the actual call stack.

 Another important point to consider is the safety of
 the actual call to [`extend`]: see its documentation.

# License
dual licensed with MIT and APACHE 2.0

[`RecRef`]: https://docs.rs/recursive_reference/*/recursive_reference/struct.RecRef.html
[`extend`]: https://docs.rs/recursive_reference/*/recursive_reference/struct.RecRef.html#method.extend