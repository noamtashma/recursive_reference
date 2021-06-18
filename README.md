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
     let node1 = Node { value : 5, next : List::Empty };
     let mut node2 = Node { value : 2, next : List::Root(Box::new(node1)) };

     let mut rec_ref = RecRef::new(&mut node2);
     assert_eq!(rec_ref.value, 2); // rec_ref is a smart pointer to the current node
     rec_ref.value = 7; // change the value at the head of the list
     RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
         List::Root(next_node) => Ok(next_node),
         List::Empty => Err(()),
     })?;
     assert_eq!(rec_ref.value, 5);
     // extend the RecRef
     let res = RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
         List::Root(next_node) => Ok(next_node),
         List::Empty => Err(()),
     });
     assert_eq!(res, Err(())); // could not go forward because it reached the end of the list
     assert_eq!(rec_ref.value, 5);
     let last = RecRef::pop(&mut rec_ref).ok_or(())?;
     assert_eq!(last.value, 5);
     assert_eq!(rec_ref.value, 7) ; // moved back to the head of the list because we popped rec_ref
     Ok(())
 }
```

 We can also wrap a [`RecRef`] in a walker struct
 ----------------------------------------------
 Note: this time we are using a `RecRef<List<T>>` and not a `RecRef<Node<T>>`, to allow pointing
 at the empty end of the list.
```rust
 use recursive_reference::*;
 struct Walker<'a, T> {
     rec_ref : RecRef<'a, List<T>>
 }
 impl<'a, T> Walker<'a, T> {
     pub fn new(list: &'a mut List<T>) -> Self {
         Walker {
             rec_ref : RecRef::new(list)
         }
     }

     /// Returns `None` when at the tail end of the list
     pub fn next(&mut self) -> Option<()> {
         RecRef::extend_result(&mut self.rec_ref, |current| match current {
             List::Empty => Err(()),
             List::Root(node) => Ok(&mut node.next),
         }).ok()
     }

     /// Returns `None` when at the head of the list
     pub fn prev(&mut self) -> Option<()> {
         RecRef::pop(&mut self.rec_ref)?;
         Some(())
     }

     /// Returns `None` when at the tail end of the list
     pub fn value_mut(&mut self) -> Option<&mut T> {
         match &mut *self.rec_ref {
             List::Root(node) => Some(&mut node.value),
             List::Empty => None,
         }
     }
 }

 fn main() -> Result<(), ()> {
     let node1 = Node { value : 5, next : List::Empty };
     let node2 = Node { value : 2, next : List::Root(Box::new(node1)) };
     let mut list = List::Root(Box::new(node2));

     let mut walker = Walker::new(&mut list);
     assert_eq!(walker.value_mut().cloned(), Some(2));
     *walker.value_mut().ok_or(())? = 7;
     walker.next().ok_or(())?;
     assert_eq!(walker.value_mut().cloned(), Some(5));
     walker.next().ok_or(())?;
     assert_eq!(walker.value_mut().cloned(), None); // end of the list
     walker.prev().ok_or(())?;
     assert_eq!(walker.value_mut().cloned(), Some(5));
     walker.prev().ok_or(())?;
     assert_eq!(walker.value_mut().cloned(), Some(7)); // we changed the value at the head
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
 
 # Safety
 The [`RecRef`] type is implemented using unsafe rust, but provides a safe interface.
 The [`RecRef`] methods' types guarantee that the references will always have a legal lifetime
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