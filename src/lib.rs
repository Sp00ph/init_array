//! A library for initializing arrays itemwise.
//!
//! Normally, when using fixed size arrays, you can only initialize them with a const value.
//! Example:
//! ```
//! // Literals work.
//! let arr = [0; 5];
//!
//! // Const values work too.
//! const STRING: String = String::new();
//! let arr = [STRING; 5];
//! ```
//!
//! ```compile_fail
//! // Function calls don't work.
//! let arr = [computation(); 5];
//! ```
//!
//! there are a few different ways of initializing an array itemwise, including:
//! * Using an array of [`Option`]s, initializing them all to [`None`] and then initializing each one to [`Some(computation())`](core::option::Option::Some).
//! * Using a [`Vec`](alloc::vec::Vec) and incrementally pushing items to it.
//! * Using an array of [`MaybeUninit`]s, gradually initializing them and then transmuting the array. This requires usage of `unsafe` code.
//!
//! This crate uses the third method but hides it behind a safe interface, so that no unsafe code is needed on the User end.
//! It provides three functions to initialize arrays itemwise:
//! * [`init_array`] to initialize a stack-based fixed-size array.
//! * [`init_boxed_array`] to initialize a heap-allocated fixed-size array.
//! * [`init_boxed_slice`] to initialize a heap-allocated dynamically-sized slice.
//!
//! There is also a `try_init_array` function which allows to initialize an array fallibly and return the error early.
//!
//! If you have the `nightly` feature enabled, you will have access to additional versions of the `init_boxed_...` functions compliant with the new Allocator API.
//!
//!
//! If you turn off the `alloc` feature, which is enabled by default, you can use this crate in a `#[no_std]` context without an allocator.
//! The crate is fully `#[no_std]` compatible.
//!
//! In addition to the 3 functions mentioned above, there are also two extension traits provided, [`ArrayExt`] and [`SliceExt`],
//! which provide the same functionality as the free functions.
//!
//! All of these functions share the property that, if the initialization of any item panics (i.e. if the stack unwinds), all the
//! already initialized items are dropped, minimizing the risk of a memory leak.
#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "nightly", feature(allocator_api, maybe_uninit_uninit_array,))]

#[cfg(feature = "alloc")]
extern crate alloc;

use core::convert::Infallible;
use core::mem::{forget, transmute_copy, MaybeUninit};
use core::ptr::{drop_in_place, slice_from_raw_parts_mut};

mod array_ext;
#[cfg_attr(not(feature = "nightly"), path = "stable.rs")]
#[cfg_attr(feature = "nightly", path = "nightly.rs")]
#[cfg(feature = "alloc")]
mod boxed;
#[cfg(feature = "alloc")]
pub use boxed::*;

pub use array_ext::*;


/// Try to initialize all the elements in a slice, returning early if
/// it fails.
///
/// For each item in the slice, the given function will be called with the
/// items index and the result be written into the slice. If the initialization
/// of any item fails, all previously initialized items will be dropped, meaning
/// that the entire slice will be uninitialized again, and the error returned by
/// `f` will be returned from the function.
///
/// # Examples
///
/// ```
/// #![feature(maybe_uninit_uninit_array)]
/// use init_array::try_init_slice;
/// use core::mem::MaybeUninit;
///
/// let mut arr = MaybeUninit::uninit_array::<5>();
///
/// assert_eq!(try_init_slice::<usize, usize, _>(&mut arr, |i| Ok(i)), Ok([0, 1, 2, 3, 4].as_mut_slice()));
/// assert_eq!(try_init_slice::<usize, usize, _>(&mut arr, |i| Err(i)), Err(0));
/// ```
#[inline]
pub fn try_init_slice<T, E, F: FnMut(usize) -> Result<T, E>>(
    s: &mut [MaybeUninit<T>],
    mut f: F,
) -> Result<&mut [T], E> {
    struct Guard<T> {
        ptr: *mut T,
        len: usize,
    }

    impl<T> Drop for Guard<T> {
        fn drop(&mut self) {
            // SAFETY: It is guaranteed that exactly `self.len` items in the slice have been initialized.
            // `self.ptr` is guaranteed to be valid, even if `T` is a ZST, because it has been passed in
            // through the slice `s`.
            unsafe { drop_in_place(slice_from_raw_parts_mut(self.ptr, self.len)) };
        }
    }

    let mut guard = Guard { ptr: s.as_mut_ptr() as *mut T, len: 0 };

    for (i, a) in s.iter_mut().enumerate() {
        // if we early return here, all the already initialzed elements in the slice
        // will be dropped by the guards Drop impl
        a.write(f(i)?);
        guard.len += 1;
    }

    forget(guard);

    // since we initialized all the elements, pointer casting to a &mut [T]
    // is sound
    Ok(unsafe { &mut *(s as *mut [MaybeUninit<T>] as *mut [T]) })
}

/// Initialize all the elements in the slice with the result of calling the function
/// with the index in the slice.
///
/// If this unwinds, all the already initalized elements will be dropped, minimizing
/// the risk of accidental resource leaks
#[inline]
pub fn init_slice<T, F: FnMut(usize) -> T>(s: &mut [MaybeUninit<T>], mut f: F) -> &mut [T] {
    unwrap_infallible(try_init_slice(s, |i| Ok(f(i))))
}

pub(crate) fn unwrap_infallible<T>(r: Result<T, Infallible>) -> T {
    r.unwrap_or_else(|i| match i {})
}

/// Initialize a fixed-sized stack-based array.
///
/// This function takes in a function, which can use the index in the array to compute the value for the item at that index.
/// The function needs to implement [`FnMut`], which means it can also carry internal mutable state which persists for all items.
///
/// Thanks to the stabilization of `min_const_generics` in Rust 1.51, you can use this function to initialize arrays of any length.
///
/// # Examples
///
/// ```
/// use init_array::init_array;
/// assert_eq!(init_array(|_| 0), [0; 3]);
///
/// assert_eq!(init_array(|i| i + 1), [1, 2, 3, 4, 5]);
///
/// let mut state = 0;
///
/// // arr[i] represents the sum of the first `i + 1` natural numbers.
/// let arr = init_array(|i| {
///     state += i + 1;
///     state
/// });
/// assert_eq!(arr, [1, 3, 6, 10, 15]);
/// ```
#[inline]
pub fn init_array<T, F, const N: usize>(mut f: F) -> [T; N]
where
    F: FnMut(usize) -> T,
{
    unwrap_infallible(try_init_array(|i| Ok(f(i))))
}

/// Does the same as [`init_array`] but supports early return for fallible
/// initialization of fixed size arrays.
///
/// # Examples
///
/// ```
/// use init_array::try_init_array;
/// assert_eq!(try_init_array::<usize, usize, _, 5>(|i| Ok(i)), Ok([0, 1, 2, 3, 4]));
///
/// assert_eq!(try_init_array::<usize, usize, _, 5>(|i| Err(i)), Err(0));
#[inline]
pub fn try_init_array<T, E, F, const N: usize>(f: F) -> Result<[T; N], E>
where
    F: FnMut(usize) -> Result<T, E>,
{
    // SAFETY: Assuming that `MaybeUninit<MaybeUninit<T>>` is initialized is safe, as the inner `MaybeUninit<T>` still
    // doesn't guarantee that the `T` is initialized, so assuming that an array of `MaybeUninit`s is initialized is
    // safe too.
    let mut arr = unsafe { MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init() };

    try_init_slice(&mut arr, f)?;

    // SAFETY: `init_slice` initializes all the items in the array, so it's safe to transmute it into the initialized type
    Ok(unsafe { transmute_copy(&arr) })
}

#[cfg(test)]
mod tests {
    use std::{
        panic::catch_unwind,
        sync::atomic::{AtomicUsize, Ordering::SeqCst},
    };

    use super::*;

    #[test]
    fn array() {
        assert_eq!(init_array::<_, _, 3>(|_| 0), [0, 0, 0]);
        assert_eq!(init_array::<_, _, 3>(|i| i), [0, 1, 2]);
        assert_eq!(init_array::<_, _, 5>(|i| i * i), [0, 1, 4, 9, 16]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn boxed_array() {
        assert_eq!(*init_boxed_array::<_, _, 3>(|_| 0), [0, 0, 0]);
        assert_eq!(*init_boxed_array::<_, _, 3>(|i| i), [0, 1, 2]);
        assert_eq!(*init_boxed_array::<_, _, 5>(|i| i * i), [0, 1, 4, 9, 16]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn boxed_slice() {
        assert_eq!(*init_boxed_slice(3, |_| 0), [0, 0, 0]);
        assert_eq!(*init_boxed_slice(3, |i| i), [0, 1, 2]);
        assert_eq!(*init_boxed_slice(5, |i| i * i), [0, 1, 4, 9, 16]);
    }

    #[cfg(feature = "alloc")]
    #[test]
    fn readme_example() {
        let arr = init_array(|i| i * i);
        assert_eq!(arr, [0, 1, 4, 9, 16]);

        let arr = init_boxed_array(|i| i * i);
        assert_eq!(arr, Box::new([0, 1, 4, 9, 16]));

        let arr = init_boxed_slice(5, |i| i * i);
        assert_eq!(&*arr, &[0, 1, 4, 9, 16]);

        let mut state = 0;
        let arr = init_array(move |i| {
            state += i + 1;
            state
        });

        assert_eq!(arr, [1, 3, 6, 10, 15, 21, 28, 36, 45, 55]);
    }

    #[test]
    fn drop() {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        struct Foo;

        impl Foo {
            fn new() -> Self {
                COUNTER.fetch_add(1, SeqCst);
                Self
            }
        }

        impl Drop for Foo {
            fn drop(&mut self) {
                COUNTER.fetch_sub(1, SeqCst);
            }
        }

        let _ = catch_unwind(|| {
            init_array::<_, _, 10>(|i| {
                if i == 7 {
                    assert_eq!(COUNTER.load(SeqCst), 6);
                    panic!()
                }
                Foo::new()
            });
            assert_eq!(COUNTER.load(SeqCst), 0);
        });

        #[cfg(feature = "alloc")]
        let _ = catch_unwind(|| {
            init_boxed_array::<_, _, 10>(|i| {
                if i == 7 {
                    assert_eq!(COUNTER.load(SeqCst), 6);
                    panic!()
                }
                Foo::new()
            });
            assert_eq!(COUNTER.load(SeqCst), 0);
        });

        #[cfg(feature = "alloc")]
        let _ = catch_unwind(|| {
            init_boxed_slice(10, |i| {
                if i == 7 {
                    assert_eq!(COUNTER.load(SeqCst), 6);
                    panic!()
                }
                Foo::new()
            });
            assert_eq!(COUNTER.load(SeqCst), 0);
        });
    }
}
