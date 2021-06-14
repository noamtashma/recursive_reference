//! Recursive reference
//! This module provides a way to traverse recursive structures easily and safely.
//! Rust's lifetime rules will usually force you to either only walk forward through the structure,
//! or use recursion, calling your method recursively every time you go down a node,
//! and returning every time you want to go back up, which leads to terrible code.
//!
//! Instead, you can use the `RecRef` type, to safely and dynamically walk up
//! and down your recursive structure.
//!
//! Say we have a recursive linked list structure:
//!```
//!enum List<T> {
//!    Root(Box<Node<T>>),
//!    Empty,
//!}
//!struct Node<T> {
//!    value: T,
//!    next: List<T>,
//!}
//!```
//!
//! We can use a RecRef directly:
//!```
//! # enum List<T> {
//! # Root(Box<Node<T>>),
//! # Empty,
//! # }
//! # struct Node<T> {
//! # value: T,
//! # next: List<T>,
//! # }
//! use recursive_reference::*;
//!
//! fn main() -> Result<(), ()> {
//!     let node1 = Node { value : 5, next : List::Empty };
//!     let mut node2 = Node { value : 2, next : List::Root(Box::new(node1)) };
//!     //let mut list = List::Root(Box::new(node2));
//!
//!     let mut rec_ref = RecRef::new(&mut node2);
//!     assert_eq!(rec_ref.value, 2);
//!     rec_ref.value = 7; // change the value at the head of the list
//!     rec_ref.extend_result(|node| match &mut node.next {
//!         List::Root(next_node) => Ok(next_node),
//!         List::Empty => Err(()),
//!     })?;
//!     assert_eq!(rec_ref.value, 5);
//!     // extend the RecRef
//!     let res = rec_ref.extend_result(|node| match &mut node.next {
//!         List::Root(next_node) => Ok(next_node),
//!         List::Empty => Err(()),
//!     });
//!     assert_eq!(res, Err(())); // could not go forward because it reached the end of the list
//!     assert_eq!(rec_ref.value, 5);
//!     let last = rec_ref.pop().ok_or(())?;
//!     assert_eq!(last.value, 5);
//!     assert_eq!(rec_ref.value, 7) ; // we changed the value at the head of the list
//!     Ok(())
//! }
//!```
//!
//! We can also wrap a RecRef in a struct allowing us to walk up and down
//! our list:
//! (Note: this time we are using a `RecRef<List<T>>` and not a `RecRef<Node<T>>`, to allow pointing
//! at the empty end of the list)
//!```
//! # enum List<T> {
//! # Root(Box<Node<T>>),
//! # Empty,
//! # }
//! # struct Node<T> {
//! # value: T,
//! # next: List<T>,
//! # }
//! use recursive_reference::*;
//! struct Walker<'a, T> {
//!     rec_ref : RecRef<'a, List<T>>
//! }
//! impl<'a, T> Walker<'a, T> {
//!     pub fn new(list: &'a mut List<T>) -> Self {
//!         Walker {
//!             rec_ref : RecRef::new(list)
//!         }
//!     }
//!
//!     /// Returns `None` when at the tail end of the list
//!     pub fn next(&mut self) -> Option<()> {
//!         self.rec_ref.extend_result(|current| match current {
//!             List::Empty => Err(()),
//!             List::Root(node) => Ok(&mut node.next),
//!         }).ok()
//!     }
//!
//!     /// Returns `None` when at the head of the list
//!     pub fn prev(&mut self) -> Option<()> {
//!         self.rec_ref.pop()?;
//!         Some(())
//!     }
//!
//!     /// Returns `None` when at the tail end of the list
//!     pub fn value_mut(&mut self) -> Option<&mut T> {
//!         match &mut *self.rec_ref {
//!             List::Root(node) => Some(&mut node.value),
//!             List::Empty => None,
//!         }
//!     }
//! }
//!
//! fn main() -> Result<(), ()> {
//!     let node1 = Node { value : 5, next : List::Empty };
//!     let node2 = Node { value : 2, next : List::Root(Box::new(node1)) };
//!     let mut list = List::Root(Box::new(node2));
//!
//!     let mut walker = Walker::new(&mut list);
//!     assert_eq!(walker.value_mut().cloned(), Some(2));
//!     *walker.value_mut().ok_or(())? = 7;
//!     walker.next().ok_or(())?;
//!     assert_eq!(walker.value_mut().cloned(), Some(5));
//!     walker.next().ok_or(())?;
//!     assert_eq!(walker.value_mut().cloned(), None); // end of the list
//!     walker.prev().ok_or(())?;
//!     assert_eq!(walker.value_mut().cloned(), Some(5));
//!     walker.prev().ok_or(())?;
//!     assert_eq!(walker.value_mut().cloned(), Some(7)); // we changed the value at the head
//!     Ok(())
//! }
//!```
//! This works by having a stack of references in the RecRef. You can do these toperations:
//! * You can always use the current reference.
//!  that is, the current reference - the RecRef is a smart pointer to it.
//! * using [`extend`][RecRef::extend], freeze the current reference
//!  and extend the RecRef with a new reference derived from it.
//!  for example, pushing to the stack the child of the current node.
//! * pop the stack to get back to the previous references, unfreezing them.
//!
//! # Safety
//! The RecRef type is implemented using unsafe rust, but provides a safe interface.
//!
//! The RecRef obeys rust's borrowing rules, by simulating freezing. Whenever
//! you extend the RecRef with a reference `child_ref` that is derived from the current
//! reference `parent_ref`, the RecRef freezes `parent_ref`, and no longer allows
//! `parent_ref` to be used.
//! When `child_ref` will be popped from the RecRef,
//! `parent_ref` will be allowed to be used again.
//!
//! This is essentially the same as what would have happened if you wrote your functions recursively,
//! but decoupled from the actual call stack.
//!
//! Another important point to consider is the safety of
//! the actual call to [`extend`][RecRef::extend] : see its documentation.
//!
//! Internally, the RecRef keeps a stack of pointers, instead of reference, in order not
//! to violate rust's invariants.

use std::marker::PhantomData;
use std::ops::Deref;
use std::ops::DerefMut;
use void::ResultVoidExt;

// TODO: switch to `NonNull` when rust 1.53 arrives.
/// A Recursive reference.
/// This struct is used to allow recursively reborrowing mutable references in a dynamic
/// but safe way.
pub struct RecRef<'a, T: ?Sized> {
    head: *mut T,
    vec: Vec<*mut T>,
    phantom: PhantomData<&'a mut T>,
}

// TODO: consider converting the pointers to values without checking for null values.
// it's supposed to work, since the pointers only ever come from references.

// these aren't ever supposed to happen. but since we touch unsafe code, we might as well
// have clear error message when we `expect()`
pub const NO_VALUE_ERROR: &str = "invariant violated: RecRef can't be empty";
pub const NULL_POINTER_ERROR: &str = "error! somehow got null pointer";

impl<'a, T: ?Sized> RecRef<'a, T> {
    /// Creates a new RecRef containing only a single reference.
    pub fn new(r: &'a mut T) -> Self {
        RecRef {
            head: r as *mut T,
            vec: vec![],
            phantom: PhantomData,
        }
    }

    /// Returns the size of the RecRef, i.e, the amount of references in it.
    /// I increases every time you extend the RecRef, and decreases every time you pop
    /// the RecRef.
    pub fn size(&self) -> usize {
        self.vec.len() + 1
    }

    /// This function extends the RecRef one time. That means, if the current
    /// reference is `current_ref: &mut T`, then this call extends the RecRef
    /// with the new reference `ref2: &mut T = func(current_ref)`.
    /// After this call, the RecRef will expose the new `ref2`, and `current_ref`
    /// will be frozen (As it is borrowed by `ref2`), until `ref2` is
    /// popped off, unfreezing `current_ref`.
    ///
    /// # Safety:
    /// The type ensures no leaking is possible, since `func` can't guarantee that
    /// `current_ref` will live for any length of time, so it can't leak it anywhere.
    /// It can only use `current_ref` inside the function, and use it in order to return `ref2`, which is the
    /// intended usage.
    ///
    /// A different point of view is this: we have to borrow `current_ref` to `func`
    /// with the actual correct lifetime: the lifetime in which it is allowed to
    /// freeze `current_ref` in order to use `ref2`.
    ///
    /// However, we don't know yet what that
    /// lifetime is: it will be whatever amount of time passes until `ref2` will be
    /// popped back, unfreezing `current_ref`. (and that lifetime can even be decided dynamically).
    /// Whatever lifetime `'freeze_time` that turns out to be, the type of `func` should have been
    /// `func: FnOnce(&'freeze_time mut T) -> &'freeze_time mut T`.
    ///
    /// Therefore, we require that `func` will be able to work with any value of `'freeze_time`, so we
    /// are sure that the code would've worked correctly if we put the correct lifetime there.
    /// So that ensures the code is safe.
    ///
    /// Another point of view is considering what other types we could have given to this function:
    /// If the type was just
    /// ```rust,ignore
    /// fn extend<'a, F : FnOnce(&'a mut T) -> &'a mut T>(&mut self, func : F)
    /// ```
    /// then this function would be unsafe,
    /// because `func` could leak the reference outside, and then the caller could immediately
    /// pop the RecRef to get another copy of the same reference.
    ///
    /// We could use
    /// ```rust,ignore
    /// fn extend<'a, F : FnOnce(&'a mut T) -> &'a mut T>(&'a mut self, func : F)
    /// ```
    ///
    /// But that would invalidate the whole point of using the RecRef - You couldn't
    /// use it after extending even once, and it couldn't be any better than a regular mutable reference.
    pub fn extend<F>(&mut self, func: F)
    where
        F: for<'b> FnOnce(&'b mut T) -> &'b mut T,
    {
        self.extend_result(|r| Ok(func(r))).void_unwrap()
    }

    /// Same as [`Self::extend`], but allows the function to return an error value.
    pub fn extend_result<E, F>(&mut self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T) -> Result<&'b mut T, E>,
    {
        self.extend_result_precise(|r, _phantom| func(r))
    }

    /// Same as [`Self::extend`], but allows the function to return an error value,
    /// and also tells the inner function that `'a : 'b` using a phantom argument.
    pub fn extend_result_precise<E, F>(&mut self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>) -> Result<&'b mut T, E>,
    {
        // The compiler has to be told explicitly that the lifetime is `'a`.
        // Otherwise the lifetime is left unconstrained.
        // It probably doesn't matter much in practice, since we specifically require `func` to be able to work
        // with any lifetime, and the references are converted to pointers immediately.
        // However, that is the "most correct" lifetime - its actual lifetime may be anything up to `'a`,
        // depending on whether the user will pop it earlier than that.
        let head_ref: &'a mut T = unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR);

        match func(head_ref, PhantomData) {
            Ok(p) => {
                self.push(p);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// This function maps the top of the RecRef. It's similar to [`Self::extend`], but
    /// it replaces the current reference instead of keeping it. See [`Self::extend`] for more details.
    pub fn map<F>(&mut self, func: F)
    where
        F: for<'b> FnOnce(&'b mut T) -> &'b mut T,
    {
        self.map_result(|r| Ok(func(r))).void_unwrap()
    }

    /// Same as [`Self::map`], but allows the function to return an error value.
    pub fn map_result<E, F>(&mut self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T) -> Result<&'b mut T, E>,
    {
        self.map_result_precise(|r, _| func(r))
    }

    /// Same as [`Self::map`], but allows the function to return an error value,
    /// and also tells the inner function that `'a : 'b` using a phantom argument.
    pub fn map_result_precise<E, F>(&mut self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>) -> Result<&'b mut T, E>,
    {
        // The compiler has to be told explicitly that the lifetime is `'a`.
        // Otherwise the lifetime is left unconstrained.
        // It probably doesn't matter much in practice, since we specifically require `func` to be able to work
        // with any lifetime, and the references are converted to pointers immediately.
        // However, that is the "most correct" lifetime - its actual lifetime may be anything up to `'a`,
        // depending on whether the user will pop it earlier than that.
        let head_ref: &'a mut T = unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR);

        match func(head_ref, PhantomData) {
            Ok(p) => {
                self.head = p as *mut T;
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// Push another reference to the RecRef, unrelated to the current one.
    /// `rec_ref.push(new_ref)` is morally equivalent to `rec_ref.extend_result_precise(move |_, _| { Ok(new_ref) })`.
    /// However, you might have some trouble making the anonymous function conform to the
    /// right type.
    pub fn push(&mut self, r: &'a mut T) {
        self.vec.push(self.head);
        self.head = r as *mut T;

        /* alternative definition using a call to `self.extend_result_precise`.
        // in order to name 'x, replace the signature with:
        // pub fn push<'x>(&'x mut self, r : &'a mut T) {
        // this is used in order to tell the closure to conform to the right type
        fn helper<'a,'x, T : ?Sized, F> (f : F) -> F where
                F : for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>)
                -> Result<&'b mut T, void::Void> + 'x
            { f }

        self.extend_result_precise(
            helper::<'a,'x>(move |_, _phantom| { Ok(r) })
        ).void_unwrap();
        */
    }

    /// Lets the user use the last reference for some time, and discards it completely.
    /// After the user uses it, the next time they inspect the RecRef, it won't be there.
    /// If the RecRef has only one reference left, this returns `None`, because
    /// the RecRef can't be empty.
    pub fn pop(&mut self) -> Option<&mut T> {
        let res = unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR);
        self.head = self.vec.pop()?; // We can't pop the original reference. In that case, Return None.
        Some(res)
    }

    /// Discards the RecRef and returns the last reference.
    /// The difference between this and using [`Self::pop`] are:
    /// * This will consume the RecRef
    /// * [`Self::pop`] will never pop the first original reference, because that would produce an
    ///   invalid RecRef. [`Self::into_ref`] will.
    pub fn into_ref(self) -> &'a mut T {
        unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR)
    }
}

impl<'a, T: ?Sized> Deref for RecRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.head.as_ref() }.expect(NULL_POINTER_ERROR)
    }
}

impl<'a, T: ?Sized> DerefMut for RecRef<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR)
    }
}

impl<'a, T : ?Sized> AsRef<T> for RecRef<'a, T> {
    fn as_ref(&self) -> &T {
        &*self
    }
}

impl<'a, T: ?Sized> AsMut<T> for RecRef<'a, T> {
    fn as_mut(&mut self) -> &mut T {
        &mut *self
    }
} 

impl<'a, T: ?Sized> From<&'a mut T> for RecRef<'a, T> {
    fn from(r: &'a mut T) -> Self {
        Self::new(r)
    }
}
