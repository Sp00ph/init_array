use crate::init_slice;
use alloc::{
	alloc::{handle_alloc_error, AllocError, Allocator, Global, Layout},
	boxed::Box,
};
use core::{mem::MaybeUninit, ptr::NonNull};

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
pub fn init_boxed_array<T, F, const N: usize>(f: F) -> Box<[T; N], Global>
where
	F: FnMut(usize) -> T,
{
	init_boxed_array_in(f, Global)
}

/// Does the same as [`init_boxed_array`], but returns an error on allocation error, instead of aborting the program.
#[inline]
pub fn try_init_boxed_array<T, F, const N: usize>(f: F) -> Result<Box<[T; N], Global>, AllocError>
where
	F: FnMut(usize) -> T
{
	try_init_boxed_array_in(f, Global)	
}

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
/// #![feature(allocator_api)]
/// use init_array::init_boxed_array_in;
/// use std::alloc::Global;
/// assert_eq!(init_boxed_array_in(|_| 0, Global), Box::new([0; 3]));
///
/// assert_eq!(init_boxed_array_in(|i| i + 1, Global), Box::new([1, 2, 3, 4, 5]));
///
/// let mut state = 0;
///
/// // arr[i] represents the sum of the first `i + 1` natural numbers.
/// let arr = init_boxed_array_in(|i| {
///     state += i + 1;
///     state
/// }, Global);
/// assert_eq!(arr, Box::new([1, 3, 6, 10, 15]));
/// ```
#[inline]
pub fn init_boxed_array_in<T, F, A, const N: usize>(f: F, alloc: A) -> Box<[T; N], A>
where
	F: FnMut(usize) -> T,
	A: Allocator,
{
	match try_init_boxed_array_in(f, alloc) {
		Ok(b) => b,
		Err(_) => handle_alloc_error(Layout::new::<[T; N]>()),
	}
}

/// Does the same as [`init_boxed_array_in`], but returns an error on allocation error, instead of aborting the program.
#[inline]
pub fn try_init_boxed_array_in<T, F, A, const N: usize>(
	f: F,
	alloc: A,
) -> Result<Box<[T; N], A>, AllocError>
where
	F: FnMut(usize) -> T,
	A: Allocator,
{
	let layout = Layout::new::<[MaybeUninit<T>; N]>();
	let ptr = if layout.size() != 0 {
		alloc.allocate(layout)?.as_ptr() as *mut [MaybeUninit<T>; N]
	} else {
		// SAFETY: If the array is zero-sized, it's safe to use a dangling pointer.
		NonNull::dangling().as_ptr()
	}
	;
	// SAFETY: We just allocated this memory, so turning it into a Box is safe. 
	let mut arr = unsafe { Box::from_raw_in(ptr, alloc) };
	init_slice(&mut *arr, f);

	// SAFETY: The entire array has been initialized, so this pointer casting is safe.
	let (ptr, alloc) = Box::into_raw_with_allocator(arr);
	Ok(unsafe { Box::from_raw_in(ptr as _, alloc) })
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
pub fn init_boxed_slice<T, F>(n: usize, f: F) -> Box<[T], Global>
where
	F: FnMut(usize) -> T,
{
	init_boxed_slice_in(n, f, Global)
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
/// #![feature(allocator_api)]
/// use init_array::init_boxed_slice_in;
/// use std::alloc::Global;
/// assert_eq!(&*init_boxed_slice_in(3, |_| 0, Global), &[0; 3]);
///
/// assert_eq!(&*init_boxed_slice_in(5, |i| i + 1, Global), &[1, 2, 3, 4, 5]);
///
/// let mut state = 0;
///
/// // arr[i] represents the sum of the first `i + 1` natural numbers.
/// let arr = init_boxed_slice_in(5, |i| {
///     state += i + 1;
///     state
/// }, Global);
/// assert_eq!(&*arr, &[1, 3, 6, 10, 15]);
/// ```
#[inline]
pub fn init_boxed_slice_in<T, F, A>(n: usize, f: F, alloc: A) -> Box<[T], A>
where
	F: FnMut(usize) -> T,
	A: Allocator,
{
	let mut arr = Box::new_uninit_slice_in(n, alloc);

	init_slice(&mut arr, f);

	// SAFETY: `init_slice` initialized the entire slice that is given to it, which in this case is the entire allocated slice.
	// Because all the items have been initialized, it's safe to transform it into the initialized slice by casting the pointer.
	let (ptr, alloc) = Box::into_raw_with_allocator(arr);
	unsafe { Box::from_raw_in(ptr as _, alloc) }
}
