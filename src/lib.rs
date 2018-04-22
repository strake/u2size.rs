#![no_std]

#![feature(asm)]

use core::ops::*;

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct u2size {
    pub msw: usize,
    pub lsw: usize,
}

impl u2size {
    #[inline]
    pub fn trailing_zeros(self) -> u32 {
        self.lsw.trailing_zeros() + (mask32(0 == self.lsw) & self.msw.trailing_zeros())
    }

    #[inline]
    pub fn count_zeros(self) -> u32 { self.lsw.count_zeros() + self.msw.count_zeros() }
    #[inline]
    pub fn count_ones(self) -> u32 { self.lsw.count_ones() + self.msw.count_ones() }

    #[inline]
    pub fn rotate_left(self, k: u32) -> Self { u2size {
        msw: shld(self.msw, self.lsw, k),
        lsw: shld(self.lsw, self.msw, k),
    } }

    #[inline]
    pub fn rotate_right(self, k: u32) -> Self { u2size {
        msw: shrd(self.msw, self.lsw, k),
        lsw: shrd(self.lsw, self.msw, k),
    } }

    #[inline]
    pub fn overflowing_add(x: Self, y: Self) -> (Self, bool) {
        let (lsw, c) = addc(x.lsw, y.lsw, false);
        let (msw, c) = addc(x.msw, y.msw, c);
        (u2size { msw, lsw }, c)
    }

    #[inline]
    pub fn overflowing_sub(x: Self, y: Self) -> (Self, bool) {
        let (lsw, c) = subc(x.lsw, y.lsw, false);
        let (msw, c) = subc(x.msw, y.msw, c);
        (u2size { msw, lsw }, c)
    }

    #[inline]
    pub fn overflowing_mul(u2size { msw: x1, lsw: x0 }: Self,
                           u2size { msw: y1, lsw: y0 }: Self) -> (Self, bool) {
        let c2 = 0 != x1 && 0 != y1;
        let (c0,  z0)  = carrying_mul(x0, y0);
        let (z1x, c1x) = usize::overflowing_mul(x0, y1);
        let (z1y, c1y) = usize::overflowing_mul(y0, x1);
        let (z1z, c1z) = usize::overflowing_add(z1x, z1y);
        let (z1, c) = addc(z1z, c0, c1z);
        (u2size { msw: z1, lsw: z0 }, c1x | c1y | c2 | c)
    }
}

impl From<usize> for u2size {
    #[inline]
    fn from(n: usize) -> Self { u2size { msw: 0, lsw: n } }
}

impl Shr<u32> for u2size {
    type Output = Self;
    #[inline]
    fn shr(self, k: u32) -> Self {
        if k < word_bits { u2size {
            msw: self.msw >> k,
            lsw: shrd(self.lsw, self.msw, k),
        } } else { Self::from(self.msw >> (k - word_bits)) }
    }
}

impl Shl<u32> for u2size {
    type Output = Self;
    #[inline]
    fn shl(self, k: u32) -> Self {
        if k < word_bits { u2size {
            msw: shld(self.msw, self.lsw, k),
            lsw: self.lsw << k,
        } } else { u2size {
            msw: self.lsw << (k - word_bits),
            lsw: 0,
        } }
    }
}

impl BitXor for u2size {
    type Output = Self;
    #[inline]
    fn bitxor(self, other: Self) -> Self {
        u2size { msw: self.msw ^ other.msw, lsw: self.lsw ^ other.lsw }
    }
}

impl BitXorAssign for u2size {
    #[inline]
    fn bitxor_assign(&mut self, other: Self) { *self = *self ^ other }
}

impl BitAnd for u2size {
    type Output = Self;
    #[inline]
    fn bitand(self, other: Self) -> Self {
        u2size { msw: self.msw & other.msw, lsw: self.lsw & other.lsw }
    }
}

impl BitAndAssign for u2size {
    #[inline]
    fn bitand_assign(&mut self, other: Self) { *self = *self & other }
}

impl BitOr for u2size {
    type Output = Self;
    #[inline]
    fn bitor(self, other: Self) -> Self {
        u2size { msw: self.msw | other.msw, lsw: self.lsw | other.lsw }
    }
}

impl BitOrAssign for u2size {
    #[inline]
    fn bitor_assign(&mut self, other: Self) { *self = *self | other }
}

impl Add for u2size {
    type Output = Self;
    #[inline]
    fn add(self, other: Self) -> Self { Self::overflowing_add(self, other).0 }
}

impl AddAssign for u2size {
    #[inline]
    fn add_assign(&mut self, other: Self) { *self = *self + other }
}

impl Sub for u2size {
    type Output = Self;
    #[inline]
    fn sub(self, other: Self) -> Self { Self::overflowing_sub(self, other).0 }
}

impl SubAssign for u2size {
    #[inline]
    fn sub_assign(&mut self, other: Self) { *self = *self - other }
}

impl Mul for u2size {
    type Output = Self;
    #[inline]
    fn mul(self, other: Self) -> Self { Self::overflowing_mul(self, other).0 }
}

impl MulAssign for u2size {
    #[inline]
    fn mul_assign(&mut self, other: Self) { *self = *self * other }
}

#[inline(always)]
fn shld(x: usize, y: usize, k: u32) -> usize {
    x << k | mask(0 == k) & y >> (k.wrapping_neg() & (word_bits - 1))
}

#[inline(always)]
fn shrd(x: usize, y: usize, k: u32) -> usize {
    x >> k | mask(0 == k) & y << (k.wrapping_neg() & (word_bits - 1))
}

#[inline(always)]
fn addc(x: usize, y: usize, c: bool) -> (usize, bool) {
    let (z, d) = usize::overflowing_add(x, y);
    (z + c as usize, d)
}

#[inline(always)]
fn subc(x: usize, y: usize, c: bool) -> (usize, bool) {
    let (z, d) = usize::overflowing_sub(x, y);
    (z - c as usize, d)
}

#[inline(always)]
fn mask(b: bool) -> usize { (b as usize).wrapping_neg() }

#[inline(always)]
fn mask32(b: bool) -> u32 { (b as u32).wrapping_neg() }

const word_bits: u32 = (::core::mem::size_of::<usize>() << 3) as u32;

#[cfg(target_arch = "x86_64")]
#[inline(always)]
fn carrying_mul(x: usize, y: usize) -> (usize, usize) {
    let mut c: usize;
    let mut z: usize;
    unsafe { asm!("mulq $3" : "=a"(z), "=d"(c) : "%a"(x), "r"(y)) }
    (c, z)
}

#[cfg(not(target_arch = "x86_64"))]
#[inline(always)]
fn carrying_mul(x: usize, y: usize) -> (usize, usize) {
    let n = 0usize.count_zeros() >> 1;
    let halves = |x| (x >> n, x & (!0 >> n));
    let ((x1, x0), (y1, y0)) = (halves(x), halves(y));
    let (z2, z0) = (x1 * y1, x0 * y0);
    let z1 = (x1 + x0) * (y1 + y0) - z2 - z0;
    let (w, c) = usize::overflowing_add(z0, z1 << n);
    (z2 + z1 >> n + c as usize, w)
}
