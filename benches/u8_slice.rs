#![feature(test)]

extern crate subtle;
extern crate test;
extern crate rand;

use test::black_box;
use test::Bencher;
use subtle::{ConditionallySwappable, ConditionallyAssignable, ConstantTimeEq, Choice};

#[bench]
fn u8_ct_eq(bencher: &mut Bencher) {
    let a: u8 = rand::random();
    let b: u8 = rand::random();
    bencher.iter(|| {
        black_box(a.ct_eq(&b))
    });
}

#[bench]
fn u64_ct_eq(bencher: &mut Bencher) {
    let a: u64 = rand::random();
    let b = rand::random();
    bencher.iter(|| {
        black_box(a.ct_eq(&b))
    });
}

#[bench]
fn u8_conditional_assign(bencher: &mut Bencher) {
    let mut a: u8 = rand::random();
    let b: u8 = rand::random();
    bencher.iter(|| {
        black_box(a.conditional_assign(&b, 1.into()))
    });
}

#[bench]
fn u64_conditional_assign(bencher: &mut Bencher) {
    let mut a: u64 = rand::random();
    let b = rand::random();
    bencher.iter(|| {
        black_box(a.conditional_assign(&b, 1.into()))
    });
}

#[bench]
fn u8_conditional_swap(bencher: &mut Bencher) {
    let mut a: u8 = rand::random();
    let mut b: u8 = rand::random();
    bencher.iter(|| {
        black_box(u8::conditional_swap(&mut a, &mut b, 1.into()))
    });
}

#[bench]
fn u64_conditional_swap(bencher: &mut Bencher) {
    let mut a: u64 = rand::random();
    let mut b = rand::random();
    bencher.iter(|| {
        black_box(u64::conditional_swap(&mut a, &mut b, 1.into()))
    });
}

#[bench]
fn u8_slice_ct_eq_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        a.ct_eq(b.as_slice())
    });
}

#[bench]
fn u8_slice_eq_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    let b = a.clone();
    bencher.iter(|| {
        black_box(a.as_slice() == b.as_slice())
    });
}

#[bench]
fn u8_slice_conditional_swap_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(<[u8]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()))
    });
    a[0] = 0;
}

#[bench]
fn u8_slice_conditional_assign_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
    a[0] = 0;
}

#[bench]
fn u8_slice_assign_1024(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(1024);
    let mut b = Vec::with_capacity(1024);
    for _ in 0..1024 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
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
    a[0] = 0;
}

#[bench]
fn u8_slice_conditional_swap_160(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(160);
    let mut b = Vec::with_capacity(160);
    for _ in 0..160 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(<[u8]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()));
    });
    a[0] = 0;
}

#[bench]
fn u8_slice_conditional_assign_160(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(160);
    let mut b = Vec::with_capacity(160);
    for _ in 0..160 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
    a[0] = 0;
}

#[bench]
fn u8_slice_conditional_swap_4096(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(4096);
    let mut b = Vec::with_capacity(4096);
    for _ in 0..4096 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(<[u8]>::conditional_swap(a.as_mut_slice(), b.as_mut_slice(), 1.into()))
    });
    a[0] = 0;
}

#[bench]
fn u8_slice_conditional_assign_4096(bencher: &mut Bencher) {
    let mut a = Vec::with_capacity(4096);
    let mut b = Vec::with_capacity(4096);
    for _ in 0..4096 {
        a.push(rand::random::<u8>());
        b.push(rand::random::<u8>());
    }
    bencher.iter(|| {
        black_box(a.conditional_assign(b.as_slice(), 1.into()))
    });
}
