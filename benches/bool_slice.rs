#![feature(test)]

extern crate subtle;
extern crate test;
extern crate rand;

use test::black_box;
use test::Bencher;
use subtle::{ConditionallySwappable, ConditionallyAssignable, ConstantTimeEq, Choice};

#[bench]
fn bool_ct_eq(bencher: &mut Bencher) {
    let a: bool = rand::random();
    let b: bool = rand::random();
    bencher.iter(|| {
        black_box(a.ct_eq(&b))
    });
}

#[bench]
fn bool_conditional_assign(bencher: &mut Bencher) {
    let mut a: bool = rand::random();
    let b: bool = rand::random();
    bencher.iter(|| {
        black_box(a.conditional_assign(&b, 1.into()))
    });
}

#[bench]
fn bool_conditional_swap(bencher: &mut Bencher) {
    let mut a: bool = rand::random();
    let mut b: bool = rand::random();
    bencher.iter(|| {
        black_box(bool::conditional_swap(&mut a, &mut b, 1.into()))
    });
}

#[bench]
fn bool_slice_ct_eq_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        a.ct_eq(b.as_slice())
    });
}

#[bench]
fn bool_slice_eq_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    let b = a.clone();
    bencher.iter(|| {
        black_box(a.as_slice() == b.as_slice())
    });
}

#[bench]
fn bool_slice_conditional_swap_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(<[bool]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()))
    });
    a[0] = false;
}

#[bench]
fn bool_slice_conditional_assign_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
    a[0] = false;
}

#[bench]
fn bool_slice_assign_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        let choice: Choice = 1.into();
        for (ai, bi) in a.iter_mut().zip(b.iter()) {
            let cpy = *ai;
            if choice.unwrap_u8() == 1 {
                *ai = *bi;
            } else {
                *ai = cpy;
            }
        }
    });
    a[0] = false;
}

#[bench]
fn bool_slice_conditional_swap_160(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(160);
    let mut b = Vec::with_capacity(160);
    for _ in 0..160 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(<[bool]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()));
    });
    a[0] = false;
}

#[bench]
fn bool_slice_conditional_assign_160(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(160);
    let mut b = Vec::with_capacity(160);
    for _ in 0..160 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
    a[0] = false;
}

#[bench]
fn bool_slice_conditional_swap_4096(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(4096);
    let mut b = Vec::with_capacity(4096);
    for _ in 0..4096 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(<[bool]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()))
    });
    a[0] = false;
}

#[bench]
fn bool_slice_conditional_assign_4096(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(4096);
    let mut b = Vec::with_capacity(4096);
    for _ in 0..4096 {
        a.push(rand::random::<bool>());
        b.push(rand::random::<bool>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
}
