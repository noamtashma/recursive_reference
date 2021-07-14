//! Recursive reference.
//!
//!This crate provides a way to traverse recursive structures easily and safely.
//!Rust's lifetime rules will usually force you to either only walk forward through the structure,
//!or use recursion, calling your method recursively every time you go down a node,
//!and returning every time you want to go back up, which leads to terrible code.
//!
//!Instead, you can use the [`RecRef`] type, to safely and dynamically walk up
//!and down your recursive structure.
//!
//!# Examples
//!
//! Say we have a recursive linked list structure
//! ----------------------------------------------
//!```rust
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
//!We can use a [`RecRef`] directly
//!----------------------------------------------
//!```rust
//!use recursive_reference::*;
//!
//! # enum List<T> {
//! #    Root(Box<Node<T>>),
//! #    Empty,
//! # }
//! # struct Node<T> {
//! #    value: T,
//! #    next: List<T>,
//! # }
//!
//!fn main() -> Result<(), ()> {
//!   // crate a list to test
//!   let node1 = Node {
//!       value: 5,
//!       next: List::Empty,
//!   };
//!   let mut node2 = Node {
//!       value: 2,
//!       next: List::Root(Box::new(node1)),
//!   };
//!
//!   // create a `RecRef`
//!   let mut rec_ref = RecRef::new(&mut node2);
//!   // rec_ref is a smart pointer to the current node
//!   assert_eq!(rec_ref.value, 2);
//!
//!   // move forward through the list
//!   RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
//!       List::Root(next_node) => Ok(next_node),
//!       List::Empty => Err(()),
//!   })?;
//!   assert_eq!(rec_ref.value, 5); // now we're at the second node
//!
//!   // pop the `RecRef`, moving it back to the head
//!   RecRef::pop(&mut rec_ref).ok_or(())?;
//!   assert_eq!(rec_ref.value, 2);
//!   Ok(())
//!}
//!```
//!
//!We can also wrap a [`RecRef`] in a walker struct
//!----------------------------------------------
//!Note: this time we are using a `RecRef<List<T>>` and not a `RecRef<Node<T>>`, to allow pointing
//!at the empty end of the list.
//!```rust
//!use recursive_reference::*;
//! # enum List<T> {
//! #    Root(Box<Node<T>>),
//! #    Empty,
//! # }
//! # struct Node<T> {
//! #    value: T,
//! #    next: List<T>,
//! # }
//!struct Walker<'a, T> {
//!   rec_ref: RecRef<'a, Node<T>>,
//!}
//!impl<'a, T> Walker<'a, T> {
//!   /// Crates a new Walker
//!   pub fn new(node: &'a mut Node<T>) -> Self {
//!       Walker {
//!           rec_ref: RecRef::new(node),
//!       }
//!   }
//!
//!   /// Returns `None` when at the tail end of the list.
//!   /// Moves to the next node.
//!   pub fn next(&mut self) -> Option<()> {
//!       RecRef::extend_result(&mut self.rec_ref, |current| match &mut current.next {
//!           List::Empty => Err(()),
//!           List::Root(node) => Ok(node),
//!       })
//!       .ok()
//!   }
//!
//!   /// Returns `None` when at the head of the list.
//!   /// Goes back to the previous node.
//!   pub fn prev(&mut self) -> Option<()> {
//!       RecRef::pop(&mut self.rec_ref)?;
//!       Some(())
//!   }
//!
//!   /// Returns `None` when at the tail end of the list.
//!   /// Returns `Some(reference)` where `reference` is a mutable reference to the current value.
//!   pub fn value_mut(&mut self) -> &mut T {
//!       &mut self.rec_ref.value
//!   }
//!}
//!
//!fn main() -> Result<(), ()> {
//!   // crate a list to test
//!   let node1 = Node {
//!       value: 5,
//!       next: List::Empty,
//!   };
//!   let mut node2 = Node {
//!       value: 2,
//!       next: List::Root(Box::new(node1)),
//!   };
//!
//!   // create a walker for the list
//!   let mut walker = Walker::new(&mut node2);
//!   // walker has mutable access to the node value
//!   assert_eq!(*walker.value_mut(), 2);
//!   // move to the next node
//!   walker.next().ok_or(())?;
//!   assert_eq!(*walker.value_mut(), 5);
//!   assert_eq!(walker.next(), None); // currently at the end of the list
//!                                    // move back
//!   walker.prev().ok_or(())?;
//!   assert_eq!(*walker.value_mut(), 2);
//!   Ok(())
//!}
//!```
//! With a [`RecRef`] you can
//! ----------------------------------------------
//! * Use the current reference (i.e, the top reference).
//!  the [`RecRef`] is a smart pointer to it.
//! * Freeze the current reference
//!  and extend the [`RecRef`] with a new reference derived from it, using [`extend`][RecRef::extend] and similar functions.
//!  for example, push to the stack a reference to the child of the current node.
//! * Pop the stack to get back to the previous reference, unfreezing it.
//!
//! # Safety
//! The [`RecRef`] type is implemented using unsafe rust, but provides a safe interface.
//! The [`RecRef`] methods' types guarantee that the references will always have a legal lifetime
//! and will respect rust's borrow rules, even if that lifetime is not known in advance.
//!
//! The [`RecRef`] obeys rust's borrowing rules, by simulating freezing. Whenever
//! you extend a [`RecRef`] with a reference `child_ref` that is derived from the current
//! reference `parent_ref`, the [`RecRef`] freezes `parent_ref`, and no longer allows
//! `parent_ref` to be used.
//! When `child_ref` will be popped from the [`RecRef`],
//! `parent_ref` will be allowed to be used again.
//!
//! This is essentially the same as what would have happened if you wrote your functions recursively,
//! but it's decoupled from the actual call stack.
//!
//! Another important point to consider is the safety of
//! the actual call to [`extend`][RecRef::extend]: see its documentation.
#![no_std]
#![doc(html_root_url = "https://docs.rs/recursive_reference/0.3.0/recursive_reference/")]

extern crate alloc;
use alloc::vec::*;

use core::marker::PhantomData;
use core::ops::{Deref, DerefMut};
use core::ptr::NonNull;
use void::ResultVoidExt;

/// A Recursive reference.
/// This struct is used to allow recursively reborrowing mutable references in a dynamic
/// but safe way.
///
/// `RecRef<'a, T>` represents a reference to a value of type `T`, with lifetime `'a`,
/// which can move recursively into and out of its subfields of the same type `T`.
///
/// With a [`RecRef`] you can
/// ----------------------------------------------
/// * Use the current reference (i.e, the top reference).
///  The [`RecRef`] is a smart pointer to it.
/// * Freeze the current reference
///  and extend the [`RecRef`] with a new reference derived from it, using [`extend`][RecRef::extend] and similar functions.
///  For example, push to the stack a reference to the child of the current node.
/// * Pop the stack to get back to the previous reference, unfreezing it.
///
/// The methods' types guarantee that the references will always have a legal lifetime
/// and will respect rust's borrow rules, even if that lifetime is not known in advance.
///
/// Internally, the [`RecRef`] stores a [`Vec`] of pointers, that it extends and pops from.

// Safety invariants (please read `RecRef::extend`'s documentation before reading this):
// The values in `vec` are allowed to alias. However:
// For any index `i`, `vec[i]` can be safely used under these conditions:
//    * all of the values in `vec[..i]` are considered frozen.
//    * all of the values in `vec[i+1..]` are gone (e.g, if they are popped from the RecRef).
//   In such a case `vec[i]` could be unfrozen, converted to a `&'x mut T` for any `'a : 'x` and used.
// Specifically, this happens when the values in `vec[i+1..]` are references produced
// through `vec[i]`.
// See `RecRef::extend`'s documentation for more details on how this is ensured.
//
// In particular, all values in `vec` have been produced from valid mutable references `&mut T`.
pub struct RecRef<'a, T: ?Sized> {
    head: NonNull<T>,
    vec: Vec<NonNull<T>>,
    phantom: PhantomData<&'a mut T>,
}

impl<'a, T: ?Sized> RecRef<'a, T> {
    /// Creates a new RecRef containing only a single reference.
    pub fn new(r: &'a mut T) -> Self {
        RecRef {
            head: NonNull::from(r),
            vec: Vec::new(),
            phantom: PhantomData,
        }
    }

    /// Returns the size of `rec_ref`, i.e, the amount of references in it.
    /// It increases every time you extend `rec_ref`, and decreases every time you pop
    /// `rec_ref`.
    /// The size of a new [`RecRef`] is always `1`.
    pub fn size(rec_ref: &Self) -> usize {
        rec_ref.vec.len() + 1
    }

    /// This function extends `rec_ref` one time. If the current
    /// reference is `current_ref: &mut T`, then this call extends `rec_ref`
    /// with the new reference `ref2: &mut T = func(current_ref)`.
    /// After this call, `rec_ref` will expose the new `ref2`, and `current_ref`
    /// will be frozen (As it is borrowed by `ref2`), until `ref2` is
    /// popped off, unfreezing `current_ref`.
    ///
    /// # Safety:
    /// Pay close attention to the type of `func`: we require that
    /// `F: for<'b> FnOnce(&'b mut T) -> &'b mut T`. That is, for every lifetime `'b`,
    /// we require that `F: FnOnce(&'b mut T) -> &'b mut T`.
    ///
    /// Let's define `'freeze_time` to be the time `ref2` will be in the [`RecRef`].
    /// That is, `'freeze_time`
    /// is the time for which `ref2` will live, and the lifetime in which `current_ref`
    /// will be frozen by `ref2`. Then, the type of `func` should have been
    /// `FnOnce(&'freeze_time mut T) -> &'freeze_time mut T`. If that woudld have been the type
    /// of `func`, the code would've followed rust's borrowing rules correctly.
    ///
    /// However, we can't know yet what that
    /// lifetime is: it will be whatever amount of time passes until the programmer decides
    /// to pop `ref2` out of the [`RecRef`]. And that hasn't even been decided at this point.
    /// Whatever lifetime `'freeze_time` that turns out to be, we will know
    /// after-the-fact that the type of `func` should have been
    /// `FnOnce(&'freeze_time mut T) -> &'freeze_time mut T`.
    ///
    /// Therefore, the solution is to require that `func` will be able to work with any value of
    /// `'freeze_time`. Then we can be
    /// sure that the code would've worked correctly if we put the correct lifetime there.
    /// Therefore, we can always pick correct lifetimes after-the-fact, so the code must be safe.
    ///
    /// Also note:
    /// The type ensures that the current reference can't be leaked outside of `func`.
    /// `func` can't guarantee that
    /// `current_ref` will live for any length of time, so it can't store it outside anywhere
    /// or give it to anything.
    /// It can only use `current_ref` while still inside `func`,
    /// and use it in order to return `ref2`, which is the
    /// intended usage.
    pub fn extend<F>(rec_ref: &mut Self, func: F)
    where
        F: for<'b> FnOnce(&'b mut T) -> &'b mut T,
    {
        Self::extend_result(rec_ref, |r| Ok(func(r))).void_unwrap()
    }

    /// Same as [`Self::extend`], but allows the function to return an error value.
    pub fn extend_result<E, F>(rec_ref: &mut Self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T) -> Result<&'b mut T, E>,
    {
        Self::extend_result_precise(rec_ref, |r, _phantom| func(r))
    }

    /// Same as [`Self::extend`], but allows the function to return an error value,
    /// and also tells the inner function that `'a : 'b` using a phantom argument.
    pub fn extend_result_precise<E, F>(rec_ref: &mut Self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>) -> Result<&'b mut T, E>,
    {
        // Safety:
        // `rec_ref.head` was produced from a `&mut T`, and by RecRef's
        // safety invariant, it can be used. Furthermore,
        // Pushing another reference derived from it into the `rec_ref` preserves
        // the safety invariant.
        //
        // To understand how the invariant is ensured (and what it means)
        // see `RecRef::extend`'s documentation.
        //
        // However, there's another assumption here.
        // The lifetime of the reference here is indeterminate.
        // It could be any value. Thus by default the compiler will choose it
        // to be extremely short, that is, only until where `NonNull::from` is called on it.
        //
        // In fact, we want this lifetime to be a lifetime we haven't chosen yet.
        // It could be anything from as short as `'_` to as long as `'a`.
        // I arbitrarily chose it to be set to `'_`.
        //
        // Essentially, we assume here that calling `func` will have the same effect
        // even if we give it the wrong lifetime. In other words, we assume some form
        // of parametricity.
        // Semantically, this is true: code can't ever access the lifetimes. All lifetime
        // information is deleted at compile time.
        // However, we also assume that rust's optimizations
        // won't change the program's meaning because we used the wrong lifetime.
        let head_ref: &'_ mut T = unsafe { rec_ref.head.as_mut() };

        match func(head_ref, PhantomData) {
            Ok(p) => {
                Self::push(rec_ref, p);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// This function maps the top of the [`RecRef`]. It's similar to [`Self::extend`], but
    /// it replaces the current reference instead of keeping it. See [`Self::extend`] for more details.
    pub fn map<F>(rec_ref: &mut Self, func: F)
    where
        F: for<'b> FnOnce(&'b mut T) -> &'b mut T,
    {
        Self::map_result(rec_ref, |r| Ok(func(r))).void_unwrap()
    }

    /// Same as [`Self::map`], but allows the function to return an error value.
    pub fn map_result<E, F>(rec_ref: &mut Self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T) -> Result<&'b mut T, E>,
    {
        Self::map_result_precise(rec_ref, |r, _| func(r))
    }

    /// Same as [`Self::map`], but allows the function to return an error value,
    /// and also tells the inner function that `'a : 'b` using a phantom argument.
    pub fn map_result_precise<E, F>(rec_ref: &mut Self, func: F) -> Result<(), E>
    where
        F: for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>) -> Result<&'b mut T, E>,
    {
        // Safety:
        // `rec_ref.head` was produced from a `&mut T`, and by RecRef's
        // safety invariant, it can be used. Furthermore,
        // Pushing another reference derived from it into the `rec_ref` preserves
        // the safety invariant.
        //
        // To understand how the invariant is ensured (and what it means)
        // see `RecRef::extend`'s documentation.
        //
        // However, there's another assumption here.
        // The lifetime of the reference here is indeterminate.
        // It could be any value. Thus by default the compiler will choose it
        // to be extremely short, that is, only until where `NonNull::from` is called on it.
        //
        // In fact, we want this lifetime to be a lifetime we haven't chosen yet.
        // It could be anything from as short as `'_` to as long as `'a`.
        // I arbitrarily chose it to be set to `'_`.
        //
        // Essentially, we assume here that calling `func` will have the same effect
        // even if we give it the wrong lifetime. In other words, we assume some form
        // of parametricity.
        // Semantically, this is true: code can't ever access the lifetimes. All lifetime
        // information is deleted at compile time.
        // However, we also assume that rust's optimizations
        // won't change the program's meaning because we used the wrong lifetime.
        
        let head_ref: &'_ mut T = unsafe { rec_ref.head.as_mut() };

        match func(head_ref, PhantomData) {
            Ok(p) => {
                rec_ref.head = NonNull::from(p);
                Ok(())
            }
            Err(e) => Err(e),
        }
    }

    /// Push another reference to the [`RecRef`], unrelated to the current one.
    /// `rec_ref.push(new_ref)` is morally equivalent to `rec_ref.extend_result_precise(move |_, _| { Ok(new_ref) })`.
    /// However, you might have some trouble making the anonymous function conform to the
    /// right type.
    pub fn push(rec_ref: &mut Self, r: &'a mut T) {
        rec_ref.vec.push(rec_ref.head);
        rec_ref.head = NonNull::from(r);

        /* alternative definition using a call to `extend_result_precise`.
        // in order to name 'x, replace the signature with:
        // pub fn push<'x>(rec_ref: &'x mut Self, r : &'a mut T) {
        // this is used in order to tell the closure to conform to the right type
        fn helper<'a,'x, T : ?Sized, F> (f : F) -> F where
                F : for<'b> FnOnce(&'b mut T, PhantomData<&'b &'a ()>)
                -> Result<&'b mut T, void::Void> + 'x
            { f }

        Self::extend_result_precise(rec_ref,
            helper::<'a,'x>(move |_, _phantom| { Ok(r) })
        ).void_unwrap();
        */
    }

    /// Lets the user use the last reference for some time, and discards it completely.
    /// After the user uses it, the next time they inspect the [`RecRef`], it won't be there.
    /// If the [`RecRef`] has only one reference left, this returns `None`, because
    /// the [`RecRef`] can't be empty.
    pub fn pop(rec_ref: &mut Self) -> Option<&mut T> {
        // Safety:
        // This pointer was produced from a `&mut T`.
        //
        // By RecRef's safety invariant, this reference can be used.
        // Whenever it's used, `rec_ref` is frozen, preventing further
        // access until this reference is dropped.
        let res = unsafe { rec_ref.head.as_mut() };
        rec_ref.head = rec_ref.vec.pop()?; // We can't pop the original reference. In that case, Return None.
        Some(res)
    }

    /// Discards the [`RecRef`] and returns the last reference.
    /// The difference between this and using [`Self::pop`] are:
    /// * This will consume the [`RecRef`]
    /// * [`Self::pop`] will never pop the first original reference, because that would produce an
    ///   invalid [`RecRef`]. [`Self::into_ref`] will.
    pub fn into_ref(mut rec_ref: Self) -> &'a mut T {
        // Safety:
        // This pointer was produced from a `&mut T`.
        //
        // By RecRef's safety invariant, this reference can be used with lifetime `'a`.
        // `rec_ref` is consumed, preventing further
        // access until this reference is dropped.
        unsafe { rec_ref.head.as_mut() }
    }
}

/// [`RecRef<T>`] represents a reference to a value of type `T`,
/// which can move recursively into and out of its subfields of the same type `T`.
/// Therefore, it implements `Deref` and `DerefMut` with `Item=T`.
impl<'a, T: ?Sized> Deref for RecRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        // Safety:
        // This pointer was produced from a `&mut T`.
        //
        // By RecRef's safety invariant, this reference can be used.
        // Whenever it's used, `rec_ref` is borrowed immutably, preventing mutable
        // access until this reference is dropped.
        unsafe { self.head.as_ref() }
    }
}

/// [`RecRef<T>`] represents a reference to a value of type `T`,
/// which can move recursively into and out of its subfields of the same type `T`.
/// Therefore, it implements `Deref` and `DerefMut` with `Item=T`.
impl<'a, T: ?Sized> DerefMut for RecRef<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        // Safety:
        // This pointer was produced from a `&mut T`.
        //
        // By RecRef's safety invariant, this reference can be used.
        // Whenever it's used, `rec_ref` is frozen, preventing further
        // access until this reference is dropped.
        unsafe { self.head.as_mut() }
    }
}

impl<'a, Q: ?Sized, T: ?Sized + AsRef<Q>> AsRef<Q> for RecRef<'a, T> {
    fn as_ref(&self) -> &Q {
        AsRef::as_ref(&**self)
    }
}

impl<'a, Q: ?Sized, T: ?Sized + AsMut<Q>> AsMut<Q> for RecRef<'a, T> {
    fn as_mut(&mut self) -> &mut Q {
        AsMut::as_mut(&mut **self)
    }
}

impl<'a, T: ?Sized> From<&'a mut T> for RecRef<'a, T> {
    fn from(r: &'a mut T) -> Self {
        Self::new(r)
    }
}

/// # Safety:
/// Behaviorally, A [`RecRef`] is the same as `&'a mut T`, and
/// should be [`Send`] for the same reason. Additionally, it contains a [`Vec`].
/// The [`Send`] instance for [`Vec`] contains the bound `A: Send` for the allocator type `A`,
/// so we should require that as well. However, we don't have direct access to the
/// default allocator type. So instead we require `Vec<&'a mut T>: Send`.
unsafe impl<'a, T: ?Sized + Send> Send for RecRef<'a, T> where Vec<&'a mut T>: Send {}

/// # Safety:
/// Behaviorally, A [`RecRef`] is the same as `&'a mut T`, and
/// should be [`Sync`] for the same reason. Additionally, it contains a [`Vec`].
/// The [`Sync`] instance for [`Vec`] contains the bound `A: Sync` for the allocator type `A`,
/// so we should require that as well. However, we don't have direct access to the
/// default allocator type. So instead we require `Vec<&'a mut T>: Sync`.
unsafe impl<'a, T: ?Sized + Sync> Sync for RecRef<'a, T> where Vec<&'a mut T>: Sync {}
