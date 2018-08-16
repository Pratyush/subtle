extern crate subtle;
use subtle::*;

#[allow(missing_docs)]
#[cfg(all(target_arch = "x86_64"))]
macro_rules! concrete_funcs {
    ($t:tt, $name:ident) => {
        pub fn $name(a: &$t, b: &$t, choice: Choice) -> $t {
            $t::conditional_select(a, b, choice)
        }
    }
}
concrete_funcs!(u8, csel_u8);
concrete_funcs!(i8, csel_i8);
concrete_funcs!(u16, csel_u16);
concrete_funcs!(i16, csel_i16);
concrete_funcs!(u32, csel_u32);
concrete_funcs!(i32, csel_i32);
concrete_funcs!(u64, csel_u64);
concrete_funcs!(i64, csel_i64);

pub fn test_i64() {
    let x: i64 = 11234532463;
    let y: i64 = -4123451243;

    let result = csel_i64(&x, &y, 0.into());
    assert_eq!(result, x);

    let result = csel_i64(&x, &y, 1.into());
    assert_eq!(result, y);
}
