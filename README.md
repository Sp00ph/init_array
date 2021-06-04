# Initialize arrays itemwise

Normally, when using fixed size arrays, you can only initialize them with a const value.

Example:

```rust
// Literals work.
let arr = [0; 5];
// Const values work too.
const STRING: String = String::new();
let arr = [STRING; 5];
```

```rust
// Function calls don't work.
let arr = [computation(); 5];
```

There are a few different ways of initializing an array itemwise, including:
* Using an array of [`Option`]s, initializing them all to [`None`] and then initializing each one to [`Some(computation())`](https://doc.rust-lang.org/core/option/enum.Option.html#variant.Some).
* Using a [`Vec`] and incrementally pushing items to it.
* Using an array of [`MaybeUninit`]s, gradually initializing them and then transmuting the array. This requires usage of `unsafe` code.

[`Vec`]: https://doc.rust-lang.org/alloc/vec/struct.Vec.html
[`Option`]: https://doc.rust-lang.org/core/option/struct.Option.html
[`None`]: https://doc.rust-lang.org/core/option/enum.Option.html#variant.None
[`MaybeUninit`]: https://doc.rust-lang.org/core/mem/union.MaybeUninit.html


This crate uses the third method but hides it behind a safe interface, so that no unsafe code is needed on the User end.
It provides three functions to initialize arrays itemwise:
* `init_array` to initialize a stack-based fixed-size array.
* `init_boxed_array` to initialize a heap-allocated fixed-size array.
* `init_boxed_slice` to initialize a heap-allocated dynamically-sized slice.

If you have the `nightly` feature enabled, you will have access to additional versions of the `init_boxed_...` functions compliant with the new Allocator API.

If you turn off the `alloc` feature, which is enabled by default, you can use this crate in a `#[no_std]` context without an allocator. 
The crate is fully `#[no_std]` compatible.

All of these functions share the property that, if the initialization of any item panics (i.e. if the stack unwinds), all the
already initialized items are dropped, minimizing the risk of a memory leak.


# Examples

```rust

use init_array::*;

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
```