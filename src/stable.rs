use crate::init_slice;
use alloc::{
	alloc::{alloc, Layout},
	boxed::Box,
};
use core::{
	mem::MaybeUninit,
	ptr::{slice_from_raw_parts_mut, NonNull},
};

/// Initialize a fixed-sized heap-allocated array.
///
/// This function takes in a function, which can use the index in the array to compute the value for the item at that index.
/// The function needs to implement [`FnMut`], which means it can also carry internal mutable state which persists for all items.
///
/// Thanks to the stabilization of `min_const_generics` in Rust 1.51, you can use this function to initialize arrays of any length.
///
/// # Examples
///
/// ```
/// use init_array::init_boxed_array;
/// assert_eq!(init_boxed_array(|_| 0), Box::new([0; 3]));
///
/// assert_eq!(init_boxed_array(|i| i + 1), Box::new([1, 2, 3, 4, 5]));
///
/// let mut state = 0;
///
/// // arr[i] represents the sum of the first `i + 1` natural numbers.
/// let arr = init_boxed_array(|i| {
///     state += i + 1;
///     state
/// });
/// assert_eq!(arr, Box::new([1, 3, 6, 10, 15]));
/// ```
#[inline]
pub fn init_boxed_array<T, F, const N: usize>(f: F) -> Box<[T; N]>
where
	F: FnMut(usize) -> T,
{
	// SAFETY: Assuming that `MaybeUninit<MaybeUninit<T>>` is initialized is safe, as the inner `MaybeUninit<T>` still
	// doesn't guarantee that the `T` is initialized, so assuming that an array of `MaybeUninit`s is initialized is
	// safe too.
	let mut arr = unsafe { Box::new(MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init()) };

	init_slice(&mut *arr, f);

	// SAFETY: `init_slice` initialized the entire slice that is given to it, which in this case is the entire array.
	// Because all the items have been initialized, it's safe to transform it into the initialized array by casting the pointer.
	unsafe { Box::from_raw(Box::into_raw(arr) as _) }
}

/// Initialize a dynamically-sized heap-allocated slice.
///
/// This function takes in the length of the returned slice as well as a function, which can use the index in the array to compute
/// the value for the item at that index. The function needs to implement [`FnMut`], which means it can also carry internal mutable
/// state which persists for all items.
///
/// # Examples
///
/// ```
/// use init_array::init_boxed_slice;
/// assert_eq!(&*init_boxed_slice(3, |_| 0), &[0; 3]);
///
/// assert_eq!(&*init_boxed_slice(5, |i| i + 1), &[1, 2, 3, 4, 5]);
///
/// let mut state = 0;
///
/// // arr[i] represents the sum of the first `i + 1` natural numbers.
/// let arr = init_boxed_slice(5, |i| {
///     state += i + 1;
///     state
/// });
/// assert_eq!(&*arr, &[1, 3, 6, 10, 15]);
/// ```
#[inline]
pub fn init_boxed_slice<T, F>(n: usize, f: F) -> Box<[T]>
where
	F: FnMut(usize) -> T,
{
	unsafe {
		let layout = Layout::array::<T>(n).expect("Layout overflow");

		// SAFETY: `Box::from_raw` gives a Box using the Global Allocator, which is also used in `alloc`, so
		// getting a Box from a pointer given by `alloc` is safe.
		let mut arr: Box<[MaybeUninit<T>]> = Box::from_raw(if layout.size() == 0 {
			// SAFETY: `NonNull::dangling` returns a pointer which is guaranteed to be
			// well aligned for `T`. This branch is hit if the slice length is 0 or if `T`
			// is a ZST. In both of these cases a dangling well aligned pointer is valid for the slice.
			slice_from_raw_parts_mut(NonNull::dangling().as_ptr(), n)
		} else {
			slice_from_raw_parts_mut(alloc(layout) as _, n)
		});

		init_slice(&mut arr, f);

		// SAFETY: `init_slice` initialized the entire slice that is given to it, which in this case is the entire allocated slice.
		// Because all the items have been initialized, it's safe to transform it into the initialized slice by casting the pointer.
		Box::from_raw(Box::into_raw(arr) as _)
	}
}
