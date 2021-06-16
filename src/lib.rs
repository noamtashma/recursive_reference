#![doc(html_root_url = "https://docs.rs/recursive_reference/0.1.1/recursive_reference/")]

//! Recursive reference.
//!
//! This module provides a way to traverse recursive structures easily and safely.
//! Rust's lifetime rules will usually force you to either only walk forward through recursive structures,
//! or use recursion, calling your method recursively every time you go down a node,
//! and returning every time you want to go back up.
//!
//! Instead, you can use the [`RecRef`] type, to safely and dynamically walk up
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
//! We can use a [`RecRef`] directly:
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
//!
//!     let mut rec_ref = RecRef::new(&mut node2);
//!     assert_eq!(rec_ref.value, 2); // rec_Ref is a smart pointer to the current node
//!     rec_ref.value = 7; // change the value at the head of the list
//!     RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
//!         List::Root(next_node) => Ok(next_node),
//!         List::Empty => Err(()),
//!     })?;
//!     assert_eq!(rec_ref.value, 5);
//!     // extend the RecRef
//!     let res = RecRef::extend_result(&mut rec_ref, |node| match &mut node.next {
//!         List::Root(next_node) => Ok(next_node),
//!         List::Empty => Err(()),
//!     });
//!     assert_eq!(res, Err(())); // could not go forward because it reached the end of the list
//!     assert_eq!(rec_ref.value, 5);
//!     let last = RecRef::pop(&mut rec_ref).ok_or(())?;
//!     assert_eq!(last.value, 5);
//!     assert_eq!(rec_ref.value, 7) ; // moved back to the head of the list because we popped rec_ref
//!     Ok(())
//! }
//!```
//!
//! We can also wrap a [`RecRef`] in a struct allowing us to walk up and down
//! our list
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
//!         RecRef::extend_result(&mut self.rec_ref, |current| match current {
//!             List::Empty => Err(()),
//!             List::Root(node) => Ok(&mut node.next),
//!         }).ok()
//!     }
//!
//!     /// Returns `None` when at the head of the list
//!     pub fn prev(&mut self) -> Option<()> {
//!         RecRef::pop(&mut self.rec_ref)?;
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
//! [`RecRef`] works by storing internally a stack of references.
//! You can do these toperations with a [`RecRef`]:
//! * You can always use the current reference (i.e, the top reference).
//!  the [`RecRef`] is a smart pointer to it.
//! * using [`extend`][RecRef::extend] and similar functions, freeze the current reference
//!  and extend the [`RecRef`] with a new reference derived from it.
//!  for example, push to the stack a reference to the child of the current node.
//! * pop the stack to get back to the previous reference, unfreezing it.
//!
//! # Safety
//! The [`RecRef`] type is implemented using unsafe rust, but provides a safe interface.
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
//! the actual call to [`extend`][RecRef::extend] : see its documentation.
//!
//! Internally, the [`RecRef`] keeps a stack of pointers, instead of reference, in order not
//! to violate rust's aliasing invariants.

use std::marker::PhantomData;
use std::ops::Deref;
use std::ops::DerefMut;
use void::ResultVoidExt;

// TODO: switch to `NonNull` when rust 1.53 arrives.
/// A Recursive reference.
/// This struct is used to allow recursively reborrowing mutable references in a dynamic
/// but safe way.
///
/// `RecRef<'a, T>` represents a reference to a value of type `T`, with lifetime `'a`,
/// which can move recursively into and out of its subfields of the same type `T`.
pub struct RecRef<'a, T: ?Sized> {
    head: *mut T,
    vec: Vec<*mut T>,
    phantom: PhantomData<&'a mut T>,
}

// TODO: consider converting the pointers to values without checking for null values.
// it's supposed to work, since the pointers only ever come from references.
// otherwise, when 1.53 rolls out, convert to `NonNull`.

// these aren't ever supposed to happen. but since we touch unsafe code, we might as well
// have clear error message when we `expect()`
const NULL_POINTER_ERROR: &str = "error! somehow got null pointer";

impl<'a, T: ?Sized> RecRef<'a, T> {
    /// Creates a new RecRef containing only a single reference.
    pub fn new(r: &'a mut T) -> Self {
        RecRef {
            head: r as *mut T,
            vec: vec![],
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
        // The compiler is told explicitly that the lifetime is `'a`.
        // Otherwise the minimal lifetime possible is chosen.
        // It probably doesn't matter, since we specifically require `func` to be able to work
        // with any lifetime, and the references are converted to pointers immediately.
        // However, that is the "most correct" lifetime - the reference's actual lifetime may
        // be anything up to `'a`,
        // depending on whether the user will pop it earlier than that.
        let head_ref: &'a mut T = unsafe { rec_ref.head.as_mut() }.expect(NULL_POINTER_ERROR);

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
        // The compiler is told explicitly that the lifetime is `'a`.
        // Otherwise the minimal lifetime possible is chosen.
        // It probably doesn't matter, since we specifically require `func` to be able to work
        // with any lifetime, and the references are converted to pointers immediately.
        // However, that is the "most correct" lifetime - the reference's actual lifetime may
        // be anything up to `'a`,
        // depending on whether the user will pop it earlier than that.
        let head_ref: &'a mut T = unsafe { rec_ref.head.as_mut() }.expect(NULL_POINTER_ERROR);

        match func(head_ref, PhantomData) {
            Ok(p) => {
                rec_ref.head = p as *mut T;
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
        rec_ref.head = r as *mut T;

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
        let res = unsafe { rec_ref.head.as_mut() }.expect(NULL_POINTER_ERROR);
        rec_ref.head = rec_ref.vec.pop()?; // We can't pop the original reference. In that case, Return None.
        Some(res)
    }

    /// Discards the [`RecRef`] and returns the last reference.
    /// The difference between this and using [`Self::pop`] are:
    /// * This will consume the [`RecRef`]
    /// * [`Self::pop`] will never pop the first original reference, because that would produce an
    ///   invalid [`RecRef`]. [`Self::into_ref`] will.
    pub fn into_ref(rec_ref: Self) -> &'a mut T {
        unsafe { rec_ref.head.as_mut() }.expect(NULL_POINTER_ERROR)
    }
}

/// [`RecRef<T>`] represents a reference to a value of type `T`,
/// which can move recursively into and out of its subfields of the same type `T`.
/// Therefore, it implements `Deref` and `DerefMut` with `Item=T`.
impl<'a, T: ?Sized> Deref for RecRef<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { self.head.as_ref() }.expect(NULL_POINTER_ERROR)
    }
}

/// [`RecRef<T>`] represents a reference to a value of type `T`,
/// which can move recursively into and out of its subfields of the same type `T`.
/// Therefore, it implements `Deref` and `DerefMut` with `Item=T`.
impl<'a, T: ?Sized> DerefMut for RecRef<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { self.head.as_mut() }.expect(NULL_POINTER_ERROR)
    }
}

impl<'a, T: ?Sized> AsRef<T> for RecRef<'a, T> {
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

/// # Safety:
/// A [`RecRef`] acts like a `&mut T`, and contains a `Vec`.
/// these are `Send` (`Vec<*mut T>` is not `Send` because
/// it contains `*mut T`, but its implementation is still safe to send).
/// Thus [`RecRef`] should be `Send`.
unsafe impl<'a, T: ?Sized + Send> Send for RecRef<'a, T> {}

/// # Safety:
/// A [`RecRef`] acts like a `&mut T`, and contains a `Vec`.
/// these are `Sync` (`Vec<*mut T>` is not `Sync` because
/// it contains `*mut T`, but its implementation is still safe to sync).
/// Thus [`RecRef`] should be `Sync`.
unsafe impl<'a, T: ?Sized + Sync> Sync for RecRef<'a, T> {}
