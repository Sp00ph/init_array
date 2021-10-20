#[cfg(feature = "alloc")]
use alloc::boxed::Box;

use self::sealed::Sealed;

mod sealed {
    pub trait Sealed {}

    impl<T, const N: usize> Sealed for [T; N] {}

    impl<T> Sealed for [T] {}
}

/// Extension trait for constant sized arrays.
///
/// Allows you to initialize an array like this:
/// ```
/// use init_array::ArrayExt;
///
/// let arr: [usize; 5] = <[usize; 5]>::generate(|i| i * i);
/// assert_eq!(arr, [0, 1, 4, 9, 16]);
///
/// let arr: Box<[usize; 5]> = <[usize; 5]>::generate_boxed(|i| i * i);
/// assert_eq!(arr, Box::new([0, 1, 4, 9, 16]));
/// ```
pub trait ArrayExt: Sealed {
    type Elem;

    fn generate<F: FnMut(usize) -> Self::Elem>(f: F) -> Self
    where
        Self: Sized;

    #[cfg(feature = "alloc")]
    fn generate_boxed<F: FnMut(usize) -> Self::Elem>(f: F) -> Box<Self>;
}

#[cfg(feature = "alloc")]
/// Extension trait for dynamically sized slices.
///
/// Allows you to initialize a boxed slice like this:
/// ```
/// use init_array::SliceExt;
///
/// let arr: Box<[usize]> = <[usize]>::generate_boxed(5, |i| i * i);
/// assert_eq!(&*arr, &[0, 1, 4, 9, 16]);
/// ```
pub trait SliceExt: Sealed {
    type Elem;

    fn generate_boxed<F: FnMut(usize) -> Self::Elem>(n: usize, f: F) -> Box<Self>;
}

impl<T, const N: usize> ArrayExt for [T; N] {
    type Elem = T;

    fn generate<F: FnMut(usize) -> Self::Elem>(f: F) -> Self
    where
        Self: Sized,
    {
        crate::init_array(f)
    }

    #[cfg(feature = "alloc")]
    fn generate_boxed<F: FnMut(usize) -> Self::Elem>(f: F) -> Box<Self> {
        crate::init_boxed_array(f)
    }
}

impl<T> SliceExt for [T] {
    type Elem = T;

    fn generate_boxed<F: FnMut(usize) -> Self::Elem>(n: usize, f: F) -> Box<Self> {
        crate::init_boxed_slice(n, f)
    }
}
