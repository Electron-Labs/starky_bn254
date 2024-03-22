// Bn254 Native

use std::ops::{Add, Sub, Neg, Mul, Div};

use std::{str::FromStr, vec};


use num_bigint::{BigUint, BigInt, Sign, ToBigInt};

use crate::big_arithmetic::{big_add, big_less_than, self};

pub const ATE_LOOP_COUNT: &'static [i8] = &[
        0, 0, 0, 1, 0, 1, 0, -1, 0, 0, 1, -1, 0, 0, 1, 0, 0, 1, 1, 0, -1, 0, 0, 1, 0, -1, 0, 0, 0,
        0, 1, 1, 1, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0, -1, 0, 0, 1, 1, 0, 0, -1, 0, 0, 0, 1, 1, 0,
        -1, 0, 0, 1, 0, 1, 1,
];


pub fn modulus() -> BigUint {
    BigUint::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208583").unwrap()
}

pub fn modulus_digits() -> Vec<u32> {
    modulus().to_u32_digits()
}

pub fn get_bn254_parameter() -> BigUint {
    BigUint::from_str("4965661367192848881").unwrap()
}

pub fn get_negate(y: &[u32; 8]) -> [u32; 8] {
    let y_bu = BigUint::new(y.to_vec());
    let neg = modulus() - y_bu;
    get_u32_vec_from_literal(neg)
}

pub fn get_g2_invert(z1: &[u32; 8], z2: &[u32; 8]) -> [[u32; 8]; 2] {
    let fp2 = Fp2([
        Fp(z1.clone()),
        Fp(z2.clone())
    ]);
    [fp2.invert().0[0].0, fp2.invert().0[1].0]
}

pub fn get_u32_carries(x: &[u32; 8], y: &[u32; 8]) -> [u32; 8] {
    let mut carries = [0u32; 8];
    let mut prev_carry = 0;
    for i in 0..8 {
        if i!=0{
            prev_carry = carries[i-1];
        }
        let z = (x[i] as u64) + (y[i] as u64) + (prev_carry as u64);
        if i!=7
         {carries[i] = (z>>32) as u32 }
    }
    carries[7] = 0;
    carries
}


pub fn multiply_by_slice(x: &[u32; 8], y: u32) -> ([u32; 9],[u32; 8]) {
    let mut res: [u32; 9] = [0u32; 9];
    let mut carries: [u32; 8] = [0u32; 8];
    let mut prev_carry = 0;
    for i in 0..8 {
        let temp = (x[i] as u64 * y as u64) + prev_carry as u64;
        let temp_res = temp as u32;
        let new_carry = (temp>>32) as u32;
        prev_carry = new_carry;
        res[i] = temp_res;
        carries[i] = prev_carry;
    }
    res[8] = prev_carry;
    (res, carries)
}

pub fn add_u32_slices(x: &[u32; 16], y: &[u32; 16]) -> ([u32; 16], [u32; 16]) {
    let mut prev_carry = 0u32;
    let mut res = [0u32; 16];
    let mut carries = [0u32; 16];
    for i in 0..16 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    (res, carries)
}

pub fn add_u32_slices_8(x: &[u32; 8], y: &[u32; 8]) -> ([u32; 8], [u32; 8]) {
    let mut prev_carry = 0u32;
    let mut res = [0u32; 8];
    let mut carries = [0u32; 8];
    for i in 0..8 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    (res, carries)
}

// assume x > y
pub fn sub_u32_slices(x: &[u32; 16], y: &[u32; 16]) -> ([u32; 16], [u32; 16]) {
    let mut prev_borrow = 0u32;
    let mut res = [0u32; 16];
    let mut borrows = [0u32; 16];
    for i in 0..16 {
        if x[i] >= y[i] + prev_borrow {
            res[i] = x[i]-y[i]-prev_borrow;
            borrows[i] = 0;
            prev_borrow = 0;
        } else {
            res[i] = ((1u64 << 32) + x[i] as u64 - y[i] as u64 - prev_borrow as u64) as u32;
            borrows[i] = 1;
            prev_borrow = 1;
        }
    }
    (res, borrows)
}

// assume x > y
pub fn sub_u32_slices_8(x: &[u32; 8], y: &[u32; 8]) -> ([u32; 8], [u32; 8]) {
    let mut prev_borrow = 0u32;
    let mut res = [0u32; 8];
    let mut borrows = [0u32; 8];
    for i in 0..8 {
        if x[i] >= y[i] + prev_borrow {
            res[i] = x[i]-y[i]-prev_borrow;
            borrows[i] = 0;
            prev_borrow = 0;
        } else {
            res[i] = ((1u64 << 32) + x[i] as u64 - y[i] as u64 - prev_borrow as u64) as u32;
            borrows[i] = 1;
            prev_borrow = 1;
        }
    }
    assert_eq!(borrows[7], 0);
    (res, borrows)
}

pub fn mul_u32_slice_8(x: &[u32; 8], y: u32) -> ([u32; 8], [u32; 8]) {
    let mut prev_carry = 0u32;
    let mut res = [0u32; 8];
    let mut carries = [0u32; 8];
    for i in 0..8 {
        let tmp = x[i] as u64 * y as u64 + prev_carry as u64;
        res[i] = tmp as u32;
        carries[i] = (tmp >> 32) as u32;
        prev_carry = carries[i];
    }
    assert_eq!(prev_carry, 0);
    (res, carries)
}

pub fn get_bits_as_array(number: u32) -> [u32; 32] {
    let mut result = [0u32; 32]; // Assuming a u32 has 32 bits

    for i in 0..32 {
        // Shift the 1 bit to the rightmost position and perform bitwise AND
        result[i] = ((number >> i) & 1) as u32;
    }

    result
}

pub fn add_u32_slices_1(x: &[u32; 24], y: &[u32; 25]) -> ([u32; 25], [u32; 24]) {
    let mut x_padded = [0u32; 25];
    x_padded[0..24].copy_from_slice(x);
    let mut prev_carry = 0u32;
    let mut res = [0u32; 25];
    let mut carries = [0u32; 24];
    for i in 0..24 {
        let s = x[i] as u64 + y[i] as u64 + prev_carry as u64;
        let sum = s as u32;
        let carry = (s >> 32) as u32;
        prev_carry = carry;
        res[i] = sum;
        carries[i] = carry;
    }
    res[24] = prev_carry;
    (res, carries)
}

pub fn egcd(a: BigUint, b: BigUint) -> BigUint {
    // if a == BigUint::from(0 as u32){
    //     (b, BigUint::from(0 as u32), BigUint::from(1 as u32))
    // } else {
    //     let (g, y, x) = egcd(b.clone()%a.clone(), a.clone());
    //     (g, x - (b.clone()*(y.clone()/a.clone())), y)
    // }
    let mut a_ = BigInt::from_biguint(Sign::Plus, a);
    let mut b_ = BigInt::from_biguint(Sign::Plus, b);

    let mut x = BigInt::from_str("0").unwrap();
    let mut y = BigInt::from_str("1").unwrap();
    let mut u = BigInt::from_str("1").unwrap();
    let mut v = BigInt::from_str("0").unwrap();

    let zero = BigInt::from_str("0").unwrap();
    while a_ != zero {
        let q = b_.clone()/a_.clone();
        let r = b_%a_.clone();
        let m = x-(u.clone()*q.clone());
        let n = y-(v.clone()*q);
        b_ = a_;
        a_ = r;
        x = u;
        y = v;
        u = m;
        v = n;
    }
    let mod_bigint = modulus().to_bigint().unwrap();
    ((x%mod_bigint.clone())+mod_bigint).to_biguint().unwrap()
}

pub fn mod_inverse(a: BigUint, m: BigUint) -> BigUint {
    egcd(a, m.clone())
    // x % m
}

pub fn fp4_square(a: Fp2, b: Fp2) -> (Fp2, Fp2) {
    let a2 = a * a;
    let b2 = b * b;
    (
        b2.mul_by_nonresidue()+a2,
        ((a+b)*(a+b)) - a2 - b2
    )
}

pub fn get_u32_vec_from_literal(x: BigUint) -> [u32; 8] {
    let mut x_u32_vec: Vec<u32> = x.to_u32_digits();
    while x_u32_vec.len() != 8 {
        x_u32_vec.push(0 as u32);
    }
    x_u32_vec.try_into().unwrap()
}

pub fn get_selector_bits_from_u32(x: u32) -> [u32; 8] {
    // assert!(x<=4096);
    let mut res = [0u32; 8];
    let mut val = x.clone();
    for i in 0..8 {
        res[i] = val&1;
        val = val >> 1;
    }
    res
}

pub fn get_u32_vec_from_literal_16(x: BigUint) -> [u32; 16] {
    let mut x_u32_vec: Vec<u32> = x.to_u32_digits();
    while x_u32_vec.len() != 16 {
        x_u32_vec.push(0 as u32);
    }
    x_u32_vec.try_into().unwrap()
}

pub fn get_div_rem_modulus_from_biguint_8(x: BigUint) -> ([u32; 8], [u32; 8]) {
    let rem = x.clone()%modulus();
    let div = x/modulus();
    (get_u32_vec_from_literal(div), get_u32_vec_from_literal(rem))
}

pub fn calc_qs(x: Fp2, y: Fp2, z: Fp2) -> (Fp2, Fp2, Fp2) {
    let ax = x * z.invert();
    let ay = y * z.invert();

    let qx = ax.clone();
    let qy = ay.clone();
    let qz = Fp2::one();
    (qx, qy, qz)
}

pub fn get_double_trace(rx: Fp2, ry: Fp2, rz: Fp2) -> Vec<Fp2> {
    let t0 = ry * ry;
    let t1 = rz * rz;
    let x0 = t1.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));

    let t2 = x0 * Fp2::coeff_b();
    let t3 = t2.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));
    let x1 = ry * rz;
    let t4 = x1.mul(Fp::get_fp_from_biguint(BigUint::from(2 as u32)));
    let x2 = t2-t0;
    let x3 = rx*rx;
    let x4 = x3.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));

    let x5 = -t4;
    let k = mod_inverse(BigUint::from(2 as u32), modulus());

    let x6 = t0-t3;
    let x7 = rx*ry;
    let x8 = x6 * x7;

    let x9 = t0 + t3;
    let x10 = x9 * Fp::get_fp_from_biguint(k.clone());
    let x11 = x10 * x10;

    let x12 = t2 * t2;
    let x13 = x12 * Fp::get_fp_from_biguint(BigUint::from(3 as u32));

    let new_rx = x8 * Fp::get_fp_from_biguint(k.clone());
    let new_ry = x11 - x13;
    let new_rz = t0 * t4;

    vec![new_rx, new_ry, new_rz, t0, t1, x0, t2, t3, x1, t4, x3, x2, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13]
}

pub fn get_add_trace(rx: Fp2, ry: Fp2, rz: Fp2, qx: Fp2, qy: Fp2) -> Vec<Fp2> {
    let bit1_t0 = qy * rz;
    let bit1_t1 = ry - bit1_t0;
    let bit1_t2 = qx * rz;
    let bit1_t3 = rx - bit1_t2;
    let bit1_t4 = bit1_t1 * qx;
    let bit1_t5 = bit1_t3 * qy;
    let bit1_t6 = bit1_t4 - bit1_t5;
    let bit1_t7 = -bit1_t1;
    let bit1_t8 = bit1_t3*bit1_t3;
    let bit1_t9 = bit1_t8 * bit1_t3;
    let bit1_t10 = bit1_t8* rx;
    let bit1_t11 = bit1_t1 * bit1_t1;
    let bit1_t12 = bit1_t11 * rz;
    let bit1_t13 = bit1_t10 * Fp::get_fp_from_biguint(BigUint::from(2 as u32));
    let bit1_t14 = bit1_t9 - bit1_t13;
    let bit1_t15 = bit1_t14 + bit1_t12;
    let bit1_t16 = bit1_t10 - bit1_t15;
    let bit1_t17 = bit1_t16 * bit1_t1;
    let bit1_t18 = bit1_t9 * ry;
    let new_rx = bit1_t3 * bit1_t15;
    let new_ry = bit1_t17 - bit1_t18;
    let new_rz = rz * bit1_t9;

    vec![
        new_rx, new_ry, new_rz, bit1_t0, bit1_t1, bit1_t2, bit1_t3,
        bit1_t4, bit1_t5, bit1_t6, bit1_t7, bit1_t8, bit1_t9, bit1_t10,
        bit1_t11, bit1_t12, bit1_t13, bit1_t14, bit1_t15, bit1_t16, bit1_t17, bit1_t18
    ]
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fp(pub(crate) [u32; 8]);

impl Fp {
    pub fn zero() -> Fp {
        Fp([0; 8])
    }

    pub fn one() -> Fp {
        let mut x = Fp([0; 8]);
        x.0[0] = 1;
        x
    }

    pub fn get_fp_from_biguint(x: BigUint) -> Fp {
        Fp(get_u32_vec_from_literal(x))
    }

    pub fn get_bitlen(&self) -> u64 {
        BigUint::new(self.0.try_into().unwrap()).bits()
    }

    pub fn get_bit(&self, idx: u64) -> bool {
        BigUint::new(self.0.try_into().unwrap()).bit(idx)
    }

    pub fn invert(&self) -> Self {
        let rhs_buint = BigUint::new(self.0.try_into().unwrap());
        let inv = mod_inverse(rhs_buint, modulus());
        Fp::get_fp_from_biguint(inv)
    }

    pub fn to_biguint(&self) -> BigUint {
        BigUint::new(self.0.to_vec())
    }
}

impl Div for Fp {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        let rhs_buint = BigUint::new(rhs.0.try_into().unwrap());
        let inv = mod_inverse(rhs_buint, modulus());
        self * Fp::get_fp_from_biguint(inv)
    }
}

impl Add for Fp {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_fp(self, rhs)
    }
}

impl Mul for Fp {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mul_fp(self, rhs)
    }
}

impl Neg for Fp {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let x: BigUint = BigUint::new(self.0.try_into().unwrap());
        Fp(get_u32_vec_from_literal(modulus()-x))
    }
}



impl Sub for Fp {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        sub_fp(self, rhs)
    }
}

pub fn add_fp(x: Fp, y: Fp) -> Fp {
    // let x_b = BigUint::new(x.0.try_into().unwrap());
    // let y_b = BigUint::new(y.0.try_into().unwrap());
    // let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    // Fp(get_u32_vec_from_literal(z))
    let x_plus_y = big_add(&x.0, &y.0);
    let mut m = modulus_digits();
    m.push(0);
    if big_less_than(&x_plus_y, &m) {
        Fp(x_plus_y[..8].try_into().unwrap())
    } else {
        let (x_plus_y_reduce, _) = big_arithmetic::big_sub(&x_plus_y, &m);
        Fp(x_plus_y_reduce[..8].try_into().unwrap())
    }
    // todo!()
}

pub fn add_fp_without_reduction(x: Fp, y: Fp) -> [u32; 8] {
    // let x_b = BigUint::new(x.0.try_into().unwrap());
    // let y_b = BigUint::new(y.0.try_into().unwrap());
    // let z = (x_b + y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    // Fp(get_u32_vec_from_literal(z))
    let x_plus_y = big_add(&x.0, &y.0);
    get_u32_vec_from_literal(BigUint::new(x_plus_y))
    // todo!()
}

pub fn mul_fp(x: Fp, y: Fp) -> Fp {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = (x_b * y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    Fp(get_u32_vec_from_literal(z))
}

pub fn mul_fp_without_reduction(x: Fp, y: Fp) -> [u32; 16] {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = x_b * y_b;
    get_u32_vec_from_literal_16(z)
}

pub fn negate_fp(x: Fp) -> Fp {
    let x: BigUint = BigUint::new(x.0.try_into().unwrap());
    Fp(get_u32_vec_from_literal(modulus()-x))
}

pub fn sub_fp(x: Fp, y: Fp) -> Fp {
    let x_b = BigUint::new(x.0.try_into().unwrap());
    let y_b = BigUint::new(y.0.try_into().unwrap());
    let z = (modulus() + x_b - y_b).modpow(&BigUint::from_str("1").unwrap(), &modulus());
    Fp(get_u32_vec_from_literal(z))
}

pub fn sum_of_products(a: Vec<Fp>, b: Vec<Fp>) -> Fp{
    let acc = a.iter().zip(b.iter()).fold(Fp([0; 8]),|acc, (a_i, b_i)| {
        add_fp(mul_fp(a_i.clone(), b_i.clone()), acc)
    });
    acc
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fp2(pub(crate) [Fp; 2]);

impl Fp2 {
    pub fn zero() -> Fp2 {
        Fp2([Fp::zero(), Fp::zero()])
    }

    pub fn one() -> Fp2 {
        Fp2([Fp::one(), Fp::zero()])
    }

    pub fn non_residue() -> Fp {
        Fp::get_fp_from_biguint(modulus()-BigUint::from(1 as u32))
    }

    pub fn coeff_b() -> Fp2 {
        Fp2(
            [
                Fp::get_fp_from_biguint(BigUint::from_str("19485874751759354771024239261021720505790618469301721065564631296452457478373").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("266929791119991161246907387137283842545076965332900288569378510910307636690").unwrap())
            ]
        )
    }

    pub fn mul_by_nonresidue(&self) -> Self {
        let non_residue = Fp2([Fp::get_fp_from_biguint(BigUint::from_str("9").unwrap()), Fp::one()]);
        *self * non_residue
    }

    pub fn invert(&self) -> Self {
        let re = self.0[0];
        let im = self.0[1];
        let factor_fp = (re * re) + (im * im);
        let factor = factor_fp.invert();
        Fp2([
            factor * re,
            factor * (-im)
        ])
    }

    pub fn to_biguint(&self) -> [BigUint; 2] {
        [
            BigUint::new(self.0[0].0.to_vec()),
            BigUint::new(self.0[1].0.to_vec()),
        ]
    }

    pub fn get_u32_slice(&self) -> [[u32;8]; 2] {
        [
            self.0[0].0,self.0[1].0
        ]
    }
}

impl Add for Fp2 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
       add_fp2(self, rhs)
    }
}

impl Mul for Fp2 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
       mul_fp2(self, rhs)
    }
}

impl Sub for Fp2 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        sub_fp2(self, rhs)
    }
}

impl Mul<Fp> for Fp2 {
    type Output = Fp2;

    fn mul(self, rhs: Fp) -> Self::Output {
        let fp2 = self.0;

        let ans = Fp2([fp2[0]*rhs, fp2[1]*rhs]);
        ans
    }
}


impl Neg for Fp2 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Fp2([self.0[0].neg(), self.0[1].neg()])
    }
}

pub fn sub_fp2(x: Fp2, y: Fp2) -> Fp2 {
    Fp2 ([sub_fp(x.0[0],y.0[0]),sub_fp(x.0[1],y.0[1])])
}

pub fn add_fp2(x: Fp2, y: Fp2) -> Fp2 {
    Fp2 ([add_fp(x.0[0],y.0[0]),add_fp(x.0[1],y.0[1])])
}

pub fn mul_fp2(x: Fp2, y: Fp2) -> Fp2 {
    let c0 = sub_fp(mul_fp(x.0[0], y.0[0]),mul_fp(x.0[1], y.0[1]));
    let c1 = add_fp(mul_fp(x.0[0], y.0[1]),mul_fp(x.0[1], y.0[0]));
    Fp2 (
        [c0, c1]
    )
}


#[derive(Clone, Copy, Debug)]
pub struct Fp6(pub(crate) [Fp;6]);

impl Fp6 {
    pub fn invert(&self) -> Self {
        let c0c1c2 = self;
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        let t0 = (c0 * c0) - (c2 * c1).mul_by_nonresidue();
        let t1 = (c2 * c2).mul_by_nonresidue() - (c0 * c1);
        let t2 = (c1 * c1) - (c0 * c2);
        let t4 = (((c2 * t1) + (c1 * t2)).mul_by_nonresidue() + (c0 * t0)).invert();
        Fp6([
            (t4*t0).0,
            (t4 * t1).0,
            (t4 * t2).0,
        ].concat().try_into().unwrap())
    }

    pub fn get_u32_slice(&self) -> [[u32; 8]; 6] {
        self.0.iter().map(|f| f.0).collect::<Vec<[u32; 8]>>().try_into().unwrap()
    }

    pub fn print(&self) {
        // println!("--- Printing Fp6 ---");
        // for i in 0..self.0.len() {
        //     let fp = Fp::get_fp_from_biguint(BigUint::new(self.0[i].0.to_vec()));
        //     println!("i -- {:?}",fp.to_biguint());
        // }
        // println!("--- Printed Fp6 ---");
    }
}

impl Add for Fp6 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_fp6(self, rhs)
    }
}

impl Sub for Fp6 {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        sub_fp6(self, rhs)
    }
}

impl Div for Fp6 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.invert()
    }
}

impl Mul for Fp6 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mul_fp6(self, rhs)
    }
}

impl Neg for Fp6 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let c0c1c2 = self;
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        Fp6([
            c0.neg().0,
            c1.neg().0,
            c2.neg().0,
        ].concat().try_into().unwrap())
    }
}

pub fn add_fp6(x: Fp6, y: Fp6) -> Fp6 {
    Fp6([
        add_fp(x.0[0],y.0[0]),
        add_fp(x.0[1],y.0[1]),
        add_fp(x.0[2],y.0[2]),
        add_fp(x.0[3],y.0[3]),
        add_fp(x.0[4],y.0[4]),
        add_fp(x.0[5],y.0[5]),
    ])
}

pub fn sub_fp6(x: Fp6, y: Fp6) -> Fp6 {
    Fp6([
        sub_fp(x.0[0],y.0[0]),
        sub_fp(x.0[1],y.0[1]),
        sub_fp(x.0[2],y.0[2]),
        sub_fp(x.0[3],y.0[3]),
        sub_fp(x.0[4],y.0[4]),
        sub_fp(x.0[5],y.0[5]),
    ])
}
/*
Fp6 -> Fp2(c0), c1, c2

    [c0.c0, c0.c1, c1.c0, c1.c1, c2.c0, c2.c1]
 */
pub fn mul_fp6(x: Fp6, y: Fp6) -> Fp6 {
    let c0 = Fp2([x.0[0], x.0[1]]);
    let c1 = Fp2([x.0[2], x.0[3]]);
    let c2 = Fp2([x.0[4], x.0[5]]);

    let r0 = Fp2([y.0[0], y.0[1]]);
    let r1 = Fp2([y.0[2], y.0[3]]);
    let r2 = Fp2([y.0[4], y.0[5]]);

    let t0 = c0*r0;
    let t1 = c1*r1;
    let t2 = c2*r2;

    let t3 = c1+c2;
    let t4 = r1+r2;
    let t5 = t3*t4;
    let t6 = t5-t1;
    let t7 = t6-t2;
    let t8 = t7.mul_by_nonresidue();
    let x = t8+t0;

    let t9 = c0+c1;
    let t10 = r0+r1;
    let t11 = t9*t10;
    let t12 = t11-t0;
    let t13 = t12-t1;
    let t14 = t2.mul_by_nonresidue();
    let y = t13+t14;

    let t15 = c0+c2;
    let t16 = r0+r2;
    let t17 = t15*t16;
    let t18 = t17-t0;
    let t19 = t18-t2;
    let z = t19+t1;

    Fp6([x.0[0], x.0[1], y.0[0], y.0[1], z.0[0], z.0[1]])
}

pub fn mul_by_nonresidue(x: [Fp; 6]) -> Fp6 {
    let mut ans: [Fp; 6] = [Fp::zero(); 6];
    let c0 = Fp2([x[4], x[5]]).mul_by_nonresidue();
    ans[0] = c0.0[0];
    ans[1] = c0.0[1];
    ans[2] = x[0];
    ans[3] = x[1];
    ans[4] = x[2];
    ans[5] = x[3];
    Fp6(ans)
}

impl Fp6 {
    pub fn multiply_by_01(&self, b0: Fp2, b1: Fp2) -> Self {
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());

        let t0 = c0*b0;
        let t1 = c1*b1;

        let t2 = c2*b1;
        let t3 = t2.mul_by_nonresidue();
        let x = t3+t0;

        let t4 = b0+b1;
        let t5 = c0+c1;
        let t6 = t4*t5;
        let t7 = t6-t0;
        let y = t7-t1;

        let t8 = c2*b0;
        let z = t8+t1;
        Fp6([
            x.0, y.0, z.0
        ].concat().try_into().unwrap())
    }

    pub fn multiply_by_1(&self, b1: Fp2) -> Self {
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());

        let t0 = c2*b1;
        let x = t0.mul_by_nonresidue();

        let y = c0*b1;

        let z = c1*b1;
        Fp6([
            x.0,
            y.0,
            z.0,
        ].concat().try_into().unwrap())
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Fp12(pub(crate) [Fp; 12]);

impl Fp12 {
    pub fn zero() -> Fp12 {
        Fp12([Fp::zero(); 12])
    }

    pub fn one() -> Fp12 {
        let mut x = [Fp::zero(); 12];
        x[0] = Fp::one();
        Fp12(x)
    }

    pub fn invert(&self) -> Self {
        let c0 = Fp6(self.0[0..6].try_into().unwrap());
        let c1 = Fp6(self.0[6..12].try_into().unwrap());
        let t = (c0 * c0 - mul_by_nonresidue((c1*c1).0)).invert();
        Fp12([
            (c0*t).0,
            (-(c1*t)).0,
        ].concat().try_into().unwrap())
    }

    pub fn print(&self) {
        println!("--- Printing Fp12 ---");
        for i in 0..self.0.len() {
            let fp = Fp::get_fp_from_biguint(BigUint::new(self.0[i].0.to_vec()));
            println!("i -- {:?}",fp.to_biguint());
        }
        println!("--- Printed Fp12 ---");
    }

    pub fn from_str(x: [&str; 12]) -> Self {
        let mut ans: Fp12 = Fp12::one();
        for i in 0..12 {
            let bu = Fp::get_fp_from_biguint(BigUint::from_str(x[i]).unwrap());
            ans.0[i] = bu;
        }
        ans
    }

    pub fn get_u32_slice(&self) -> [[u32; 8]; 12] {
        self.0.iter().map(|f| f.0).collect::<Vec<[u32; 8]>>().try_into().unwrap()
    }
}

impl Add for Fp12 {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        add_fp12(self, rhs)
    }
}

impl Mul for Fp12 {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        mul_fp_12(self, rhs)
    }
}

impl Div for Fp12 {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.invert()
    }
}

impl Neg for Fp12 {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        let c3 = Fp2(self.0[6..8].to_vec().try_into().unwrap());
        let c4 = Fp2(self.0[8..10].to_vec().try_into().unwrap());
        let c5 = Fp2(self.0[10..12].to_vec().try_into().unwrap());
        Fp12([
            c0.neg().0,
            c1.neg().0,
            c2.neg().0,
            c3.neg().0,
            c4.neg().0,
            c5.neg().0,
        ].concat().try_into().unwrap())
    }
}

// impl Debug for Fp12 {
//     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
//         f.debug_tuple("Fp12").field(&self.0).finish()
//     }
// }

pub fn add_fp12(x: Fp12, y: Fp12) -> Fp12 {
    let mut ans: [Fp; 12] = [Fp::zero(); 12];
    for i in 0..12 {
        ans[i] = add_fp(x.0[i], y.0[i]);
    }
    Fp12(ans)
}

pub fn mul_fp_12(x: Fp12, y: Fp12) -> Fp12 {
    let c0 = Fp6(x.0[0..6].try_into().unwrap());
    let c1 = Fp6(x.0[6..12].try_into().unwrap());
    let r0 = Fp6(y.0[0..6].try_into().unwrap());
    let r1 = Fp6(y.0[6..12].try_into().unwrap());

    let t0 = c0*r0;
    let t1 = c1*r1;
    let t2 = mul_by_nonresidue(t1.0);
    let x = t0+t2;

    let t3 = c0+c1;
    let t4 = r0+r1;
    let t5 = t3*t4;
    let t6 = t5-t0;
    let y = t6-t1;

    Fp12([x.0, y.0].concat().try_into().unwrap())
}

impl Fp2 {

    pub fn forbenius_coefficients() -> [Fp; 2] {
        [
            Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
            Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208582").unwrap()),
        ]
    }
    pub fn forbenius_map(&self, pow: usize) -> Self {
        let constants = Fp2::forbenius_coefficients();
        Fp2([
            self.0[0],
            self.0[1]*constants[pow%2]
            ])
        }

        pub fn twist_mul_by_q_x() -> Fp2 {
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21575463638280843010398324269430826099269044274347216827212613867836435027261").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("10307601595873709700152284273816112264069230130616436755625194854815875713954").unwrap()),
            ])
        }
        pub fn twist_mul_by_q_y() -> Fp2 {
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2821565182194536844548159561693502659359617185244120367078079554186484126554").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("3505843767911556378687030309984248845540243509899259641013678093033130930403").unwrap()),
            ])
        }
}

impl Fp2 {
    pub fn double_in_place(rx: &mut Self, ry: &mut Self, rz: &mut Fp2) -> [Self; 3] {
        let t0 = (*ry) * (*ry);
        let t1 = (*rz) * (*rz);
        let x0 = t1.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));

        let t2 = x0 * Fp2::coeff_b();
        let t3 = t2.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));
        let x1 = (*ry) * (*rz);
        let t4 = x1.mul(Fp::get_fp_from_biguint(BigUint::from(2 as u32)));
        let x2 = t2-t0;
        let x3 = (*rx)*(*rx);
        let x4 = x3.mul(Fp::get_fp_from_biguint(BigUint::from(3 as u32)));

        let x5 = -t4;
        let ell_coeff = [x5, x4, x2];
        let k = mod_inverse(BigUint::from(2 as u32), modulus());

        let x6 = t0-t3;
        let x7 = (*rx)*(*ry);
        let x8 = x6 * x7;

        let x9 = t0 + t3;
        let x10 = x9 * Fp::get_fp_from_biguint(k.clone());
        let x11 = x10 * x10;

        let x12 = t2 * t2;
        let x13 = x12 * Fp::get_fp_from_biguint(BigUint::from(3 as u32));

        *rx = x8 * Fp::get_fp_from_biguint(k.clone());
        *ry = x11 - x13;
        *rz = t0 * t4;
        ell_coeff
    }

    pub fn add_in_place(rx: &mut Self, ry: &mut Self, rz: &mut Fp2, qx: &Self, qy: &Self) -> [Self; 3] {
        let bit1_t0 = (*qy) * (*rz);
        let bit1_t1 = (*ry) - bit1_t0;
        let bit1_t2 = (*qx) * (*rz);
        let bit1_t3 = (*rx) - bit1_t2;
        let bit1_t4 = bit1_t1 * (*qx);
        let bit1_t5 = bit1_t3 * (*qy);
        let bit1_t6 = bit1_t4 - bit1_t5;
        let bit1_t7 = -bit1_t1;
        let ell_coeff = [
            bit1_t3,
            bit1_t7,
            bit1_t6
        ];
        let bit1_t8 = bit1_t3*bit1_t3;
        let bit1_t9 = bit1_t8 * bit1_t3;
        let bit1_t10 = bit1_t8* (*rx);
        let bit1_t11 = bit1_t1 * bit1_t1;
        let bit1_t12 = bit1_t11 * (*rz);
        let bit1_t13 = bit1_t10 * Fp::get_fp_from_biguint(BigUint::from(2 as u32));
        let bit1_t14 = bit1_t9 - bit1_t13;
        let bit1_t15 = bit1_t14 + bit1_t12;
        *rx = bit1_t3 * bit1_t15;
        let bit1_t16 = bit1_t10 - bit1_t15;
        let bit1_t17 = bit1_t16 * bit1_t1;
        let bit1_t18 = bit1_t9 * (*ry);
        *ry = bit1_t17 - bit1_t18;
        *rz = (*rz) * bit1_t9;

        ell_coeff
    }
}

impl Fp6 {

    pub fn forbenius_coefficients_1() -> [Fp2; 6] {
        [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21575463638280843010398324269430826099269044274347216827212613867836435027261").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("10307601595873709700152284273816112264069230130616436755625194854815875713954").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275220042445260109153167277707414472061641714758635765020556616").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("3772000881919853776433695186713858239009073593817195771773381919316419345261").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("2236595495967245188281701248203181795121068902605861227855261137820944008926").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2203960485148121921418603742825762020974279258880205651966").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("18429021223477853657660792034369865839114504446431234726392080002137598044644").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("9344045779998320333812420223237981029506012124075525679208581902008406485703").unwrap()),
            ]),
        ]
    }

    pub fn forbenius_coefficients_2() -> [Fp2; 6] {
        [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2581911344467009335267311115468803099551665605076196740867805258568234346338").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("19937756971775647987995932169929341994314640652964949448313374472400716661030").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2203960485148121921418603742825762020974279258880205651966").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("5324479202449903542726783395506214481928257762400643279780343368557297135718").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("16208900380737693084919495127334387981393726419856888799917914180988844123039").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275220042445260109153167277707414472061641714758635765020556616").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("13981852324922362344252311234282257507216387789820983642040889267519694726527").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("7629828391165209371577384193250820201684255241773809077146787135900891633097").unwrap()),
            ]),
        ]
    }

    pub fn forbenius_map(&self, pow: usize) -> Self {
        let fp6_frobenius_coefficients_1 = Fp6::forbenius_coefficients_1();

        let fp6_frobenius_coefficients_2 = Fp6::forbenius_coefficients_2();
        let c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        Fp6([
            c0.forbenius_map(pow).0,
            (c1.forbenius_map(pow) * fp6_frobenius_coefficients_1[pow%6]).0,
            (c2.forbenius_map(pow) * fp6_frobenius_coefficients_2[pow%6]).0,
        ].concat().try_into().unwrap())
    }
}

impl Fp12 {
    pub fn forbenius_coefficients() -> [Fp2; 12] {
        [
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("8376118865763821496583973867626364092589906065868298776909617916018768340080").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("16469823323077808223889137241176536799009286646108169935659301613961712198316").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275220042445260109153167277707414472061641714758635765020556617").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("11697423496358154304825782922584725312912383441159505038794027105778954184319").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("303847389135065887422783454877609941456349188919719272345083954437860409601").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275220042445260109153167277707414472061641714758635765020556616").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("3321304630594332808241809054958361220322477375291206261884409189760185844239").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("5722266937896532885780051958958348231143373700109372999374820235121374419868").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208582").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("13512124006075453725662431877630910996106405091429524885779419978626457868503").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("5418419548761466998357268504080738289687024511189653727029736280683514010267").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2203960485148121921418603742825762020974279258880205651966").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("10190819375481120917420622822672549775783927716138318623895010788866272024264").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("21584395482704209334823622290379665147239961968378104390343953940207365798982").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("2203960485148121921418603742825762020974279258880205651967").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap()),
            ]),
            Fp2([
                Fp::get_fp_from_biguint(BigUint::from_str("18566938241244942414004596690298913868373833782006617400804628704885040364344").unwrap()),
                Fp::get_fp_from_biguint(BigUint::from_str("16165975933942742336466353786298926857552937457188450663314217659523851788715").unwrap()),
            ]),
        ]
    }

    pub fn forbenius_map(&self, pow: usize) -> Self {
        let fp12_forbenius_coefficients = Fp12::forbenius_coefficients();
        let r0 = Fp6(self.0[0..6].to_vec().try_into().unwrap()).forbenius_map(pow);
        let c0c1c2 = Fp6(self.0[6..12].to_vec().try_into().unwrap()).forbenius_map(pow);
        let c0 = Fp2(c0c1c2.0[0..2].to_vec().try_into().unwrap());
        let c1 = Fp2(c0c1c2.0[2..4].to_vec().try_into().unwrap());
        let c2 = Fp2(c0c1c2.0[4..6].to_vec().try_into().unwrap());
        let coeff = fp12_forbenius_coefficients[pow % 12];
        Fp12([
            r0.0,
            [(c0*coeff).0, (c1*coeff).0, (c2*coeff).0].concat().try_into().unwrap()
        ].concat().try_into().unwrap())

    }
}

impl Fp12 {
    pub fn multiply_by_034(&self, c0: Fp2, c3: Fp2, c4: Fp2) -> Self {
        let self_c0_c0 = Fp2(self.0[0..2].to_vec().try_into().unwrap());
        let self_c0_c1 = Fp2(self.0[2..4].to_vec().try_into().unwrap());
        let self_c0_c2 = Fp2(self.0[4..6].to_vec().try_into().unwrap());
        let self_c0 = Fp6(self.0[0..6].to_vec().try_into().unwrap());
        let self_c1 = Fp6(self.0[6..12].to_vec().try_into().unwrap());

        let a0 = self_c0_c0 * c0;
        let a1 = self_c0_c1 * c0;
        let a2 = self_c0_c2 * c0;
        let a_raw_vec = [a0.0, a1.0, a2.0].concat();
        let a = Fp6(a_raw_vec.try_into().unwrap());

        let mut b = Fp6(self.0[6..12].try_into().unwrap());
        b = b.multiply_by_01(c3, c4);

        let c0 = c0 + c3;
        let c1 = c4;
        let mut e = self_c0 + self_c1;
        e = e.multiply_by_01(c0, c1);

        let new_c1 = e - (a + b);
        let mut new_c0 = b;
        new_c0 = mul_by_nonresidue(new_c0.0);
        new_c0 = new_c0 + a;
        Fp12([new_c0.0, new_c1.0].concat().try_into().unwrap())
    }

    pub fn conjugate_in_place(&mut self) {
        let mut x = self.0.clone();
        for i in 6..12 {
            x[i] = -x[i];
        }
        *self = Fp12(x);
    }

    pub fn cyclotomic_square(&self) -> Self {
        let two = Fp::get_fp_from_biguint(BigUint::from(2 as u32));

        let c0c0 = Fp2(self.0[0..2].try_into().unwrap());
        let c0c1 = Fp2(self.0[2..4].try_into().unwrap());
        let c0c2 = Fp2(self.0[4..6].try_into().unwrap());
        let c1c0 = Fp2(self.0[6..8].try_into().unwrap());
        let c1c1 = Fp2(self.0[8..10].try_into().unwrap());
        let c1c2 = Fp2(self.0[10..12].try_into().unwrap());

        let t0 = fp4_square(c0c0, c1c1);
        let t1 = fp4_square(c1c0, c0c2);
        let t2 = fp4_square(c0c1, c1c2);
        let t3 = t2.1.mul_by_nonresidue();

        let t4 = t0.0 - c0c0;
        let t5 = t4 * two;
        let c0 = t5 + t0.0;

        let t6 = t1.0 - c0c1;
        let t7 = t6 * two;
        let c1 = t7 + t1.0;

        let t8 = t2.0 - c0c2;
        let t9 = t8 * two;
        let c2 = t9 + t2.0;

        let t10 = t3 + c1c0;
        let t11 = t10 * two;
        let c3 = t11 + t3;

        let t12 = t0.1 + c1c1;
        let t13 = t12 * two;
        let c4 = t13 + t0.1;

        let t14 = t1.1 + c1c2;
        let t15 = t14 * two;
        let c5 = t15 + t1.1;

        Fp12([
            c0.0,
            c1.0,
            c2.0,
            c3.0,
            c4.0,
            c5.0,
        ].concat().try_into().unwrap())
    }

    pub fn exp_by_neg_x(&self) -> Fp12 {
        let mut f = self.cyclotocmic_exponent();
        f.cyclotomic_inverse_in_place();
        f
    }

    pub fn cyclotocmic_exponent(&self) -> Fp12 {
        let mut z = Fp12::one();
        for i in (0..get_bn254_parameter().bits()).rev() {
            z = z.cyclotomic_square();
            if get_bn254_parameter().bit(i) {
                z = z * self.clone();
            }
        }
        z
    }

    pub fn cyclotomic_inverse_in_place(&mut self) {
        if *self != Fp12::zero() {
            self.conjugate_in_place();
        }
    }

    pub fn final_exponentiate(self) -> Self {
        let mut f1 = self.clone();
        f1.cyclotomic_inverse_in_place();
        let mut f2 = self.invert();

        let mut r = f1 * f2;
        f2 = r;
        r = r.forbenius_map(2);

        r = r * f2;
        let y0 = r.exp_by_neg_x();
        let y1 = y0.cyclotomic_square();
        let y2 = y1.cyclotomic_square();
        let mut y3 = y2 * y1;
        let y4 = y3.exp_by_neg_x();
        let y5 = y4.cyclotomic_square();
        let mut y6 = y5.exp_by_neg_x();
        y3.cyclotomic_inverse_in_place();
        y6.cyclotomic_inverse_in_place();
        let y7 = y6 * y4;
        let mut y8 = y7 * y3;
        let y9 = y8 * y1;
        let y10 = y8 * y4;
        let y11 = y10 * r;
        let mut y12 = y9;
        y12 = y12.forbenius_map(1);
        let y13 = y12 * y11;
        y8 = y8.forbenius_map(2);
        let y14 = y8 * y13;
        r.cyclotomic_inverse_in_place();
        let mut y15 = r * y9;
        y15 = y15.forbenius_map(3);
        let y16 = y15 * y14;
        y16
    }
}


pub fn inverse_fp2(x: Fp2) -> Fp2 {
    let t0 = x.0[0] * x.0[0];
    let t1 = x.0[1] * x.0[1];
    let t2 = t0 - (t1 * Fp2::non_residue());
    let t3 = Fp::one()/t2;
    Fp2([x.0[0]*t3, -(x.0[1]*t3)])
}


pub fn calc_pairing_precomp(x: Fp2, y: Fp2, z: Fp2) -> Vec<[Fp2; 3]> {
    let (qx, qy, qz) = calc_qs(x, y, z);

    let qy_neg = -qy.clone(); // only y gets negated in affine

    let mut rx = qx.clone();
    let mut ry = qy.clone();
    let mut rz = qz.clone();

    let mut ell_coeff: Vec<[Fp2; 3]> = Vec::<[Fp2; 3]>::new();

    for bit in ATE_LOOP_COUNT.iter().rev().skip(1) {
        ell_coeff.push(Fp2::double_in_place(&mut rx, &mut ry, &mut rz));
        match bit {
            1 => ell_coeff.push(Fp2::add_in_place(&mut rx, &mut ry, &mut rz, &qx, &qy)),
            -1 => ell_coeff.push(Fp2::add_in_place(&mut rx, &mut ry, &mut rz, &qx, &qy_neg)),
            _ => continue
        }
    }

    let mut q1x = qx.clone();
    let mut q1y = qy.clone();
    q1x = q1x.forbenius_map(1);
    q1x = q1x * Fp2::twist_mul_by_q_x();
    q1y = q1y.forbenius_map(1);
    q1y = q1y * Fp2::twist_mul_by_q_y();


    let mut q2x = q1x.clone();
    let mut q2y = q1y.clone();
    q2x = q2x.forbenius_map(1);
    q2x = q2x * Fp2::twist_mul_by_q_x();
    q2y = q2y.forbenius_map(1);
    q2y = q2y * Fp2::twist_mul_by_q_y();

    q2y = -q2y;
    ell_coeff.push(Fp2::add_in_place(&mut rx, &mut ry, &mut rz, &q1x, &q1y));
    ell_coeff.push(Fp2::add_in_place(&mut rx, &mut ry, &mut rz, &q2x, &q2y));
    return ell_coeff;
}

pub fn ell(f: &mut Fp12, coeff: [Fp2; 3], g1_x: Fp, g1_y: Fp) {
    let mut c0 = coeff[0];
    let mut c1 = coeff[1];
    let c2 = coeff[2];

    c0 = c0 * g1_y;
    c1 = c1 * g1_x;

    *f = f.multiply_by_034(c0, c1, c2);
}

pub fn miller_loop(g1_x: Fp, g1_y: Fp, g2_x: Fp2, g2_y: Fp2, g2_z: Fp2) -> Fp12 {
    let precomputes = calc_pairing_precomp(g2_x, g2_y, g2_z);
    let mut f =  Fp12::one();
    let mut j =  0;
    for i in (1..ATE_LOOP_COUNT.len()).rev() {
        if i != ATE_LOOP_COUNT.len() - 1 {
            f = f * f;
        }

        ell(&mut f, precomputes[j], g1_x, g1_y);
        j += 1;
        let bit = ATE_LOOP_COUNT[i - 1];
        if bit == 1 || bit == -1 {
            ell(&mut f, precomputes[j], g1_x, g1_y);
            j += 1;
        }

    }
    ell(&mut f, precomputes[j], g1_x, g1_y);
    j += 1;
    ell(&mut f, precomputes[j], g1_x, g1_y);
    j += 1;

    f
}

pub fn pairing(p_x: Fp, p_y: Fp, q_x: Fp2, q_y: Fp2, q_z: Fp2) -> Fp12 {
    let looped = miller_loop(p_x, p_y, q_x, q_y, q_z);
    looped
    // looped.final_exponentiate()
}


// pub fn verify_bls_signatures() -> bool {
//     // Public key
//     // Splits into little endian
//     let pk_x = BigUint::from_str("1216495682195235861952885506871698490232894470117269383940381148575524314493849307811227440691167647909822763414941").unwrap().to_u32_digits();
//     let pk_y = BigUint::from_str("2153848155426317245700560287567131132765685008362732985860101000686875894603366983854567186180519945327668975076337").unwrap().to_u32_digits();
//     // Hashed message in g2
//     let hm_x1 = BigUint::from_str("2640504383352253166624742184946918613522392710628037055952404127879364455194422343335555527925815834654853618706317").unwrap().to_u32_digits();
//     let hm_x2 = BigUint::from_str("3512267754584411844719003222712149130451230828216813699108449950001725181635151866954918805409098715392393669496763").unwrap().to_u32_digits();
//     let hm_y1 = BigUint::from_str("1819141142055458317635768413798746444112487913647217792452244858223746035103974374419118545961357374373926748974853").unwrap().to_u32_digits();
//     let hm_y2 = BigUint::from_str("2023172707753915325613231249141956147838197708174300845595677034762003254300804275953249871078804883738174492552197").unwrap().to_u32_digits();
//     let hm_z1 = BigUint::from_str("2090317837686632453881173016321367129380434356038329533464948735487686003804511165163385664859654015333500347340874").unwrap().to_u32_digits();
//     let hm_z2 = BigUint::from_str("3589273988676721566549754197317344469206294207551897598521700599244392528027952567094835689880190836504376087662460").unwrap().to_u32_digits();
//     // Generator
//     let gx = BigUint::from_str("3685416753713387016781088315183077757961620795782546409894578378688607592378376318836054947676345821548104185464507").unwrap().to_u32_digits();
//     let gy = BigUint::from_str("1339506544944476473020471379941921221584933875938349620426543736416511423956333506472724655353366534992391756441569").unwrap().to_u32_digits();
//     // Signature
//     let s_x1 = BigUint::from_str("2623971017592927791661443929103810896934774536775525535423614243457684905034147949323467412106133456094022067726851").unwrap().to_u32_digits();
//     let s_x2 = BigUint::from_str("2791552278788393998835490815906332650385266234676766868498515429583366873304026057923442494886948609285829286788356").unwrap().to_u32_digits();
//     let s_y1 = BigUint::from_str("1392880899106984160179818268515214962705329372907929072981217458923190202387659009520579695608141992620405977748755").unwrap().to_u32_digits();
//     let s_y2 = BigUint::from_str("2607207514294746608778464853061537277878553458184247374568293197687045701239874275081091959210122811260239467513958").unwrap().to_u32_digits();
//     let s_z1 = BigUint::from_str("1").unwrap().to_u32_digits();
//     let s_z2 = BigUint::from_str("0").unwrap().to_u32_digits();

//     // 1. negate Signature
//     let pk_x_negate = pk_x.clone();
//     let pk_y_negate = (modulus()-BigUint::new(pk_y)).to_u32_digits();

//     let pk_x_neg_fp = Fp::get_fp_from_biguint(BigUint::new(pk_x_negate));
//     let pk_y_neg_fp = Fp::get_fp_from_biguint(BigUint::new(pk_y_negate));

//     let hmx_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(hm_x1)), Fp::get_fp_from_biguint(BigUint::new(hm_x2))]);
//     let hmy_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(hm_y1)), Fp::get_fp_from_biguint(BigUint::new(hm_y2))]);
//     let hmz_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(hm_z1)), Fp::get_fp_from_biguint(BigUint::new(hm_z2))]);


//     let sx_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(s_x1)), Fp::get_fp_from_biguint(BigUint::new(s_x2))]);
//     let sy_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(s_y1)), Fp::get_fp_from_biguint(BigUint::new(s_y2))]);
//     let sz_fp2 = Fp2([Fp::get_fp_from_biguint(BigUint::new(s_z1)), Fp::get_fp_from_biguint(BigUint::new(s_z2))]);

//     let g_x = Fp::get_fp_from_biguint(BigUint::new(gx));
//     let g_y = Fp::get_fp_from_biguint(BigUint::new(gy));
//     // 2. P(pk_negate, Hm)
//     let e_p_hm = pairing(pk_x_neg_fp, pk_y_neg_fp, hmx_fp2, hmy_fp2, hmz_fp2);
//     let e_g_s = pairing(g_x, g_y, sx_fp2, sy_fp2, sz_fp2);

//     let mu = e_p_hm * e_g_s;

//     let mu_finaexp = mu.final_exponentiate();

//     mu_finaexp == Fp12::one()
// }

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use num_bigint::BigUint;

    use crate::native::sub_u32_slices_8;

    use super::{Fp12, modulus, get_u32_vec_from_literal, Fp, Fp2, miller_loop};

    // #[test]
    // pub fn test_bls_signature_verification() {
    //     assert!(verify_bls_signatures());
    // }

    #[test]
    fn test_subu32() {
        let x: BigUint = BigUint::from_str("1").unwrap() << 254;
        let y = modulus();
        let x_u32 = get_u32_vec_from_literal(x.clone());
        let y_u32 = get_u32_vec_from_literal(y.clone());
        let (res, _carries) = sub_u32_slices_8(&x_u32, &y_u32);
        assert_eq!( x-y, BigUint::new(res.to_vec()));
    }

    #[test]
    fn test_pairing() {
        let g1_x = Fp::get_fp_from_biguint(BigUint::from_str("792388485035126972924700782451696644186473100389722973815184405301748249").unwrap());
        let g1_y = Fp::get_fp_from_biguint(BigUint::from_str("462588485035126972924700782451696644186473100389722973815184405301741234").unwrap());
        let g2_x = Fp2([Fp::get_fp_from_biguint(BigUint::from_str("568988485035126972924700782451696644186473100389722973815184405301748249").unwrap()), Fp::get_fp_from_biguint(BigUint::from_str("891288485035126972924700782451696644186473100389722973815184405301748249").unwrap())]);
        let g2_y = Fp2([Fp::get_fp_from_biguint(BigUint::from_str("467888485035126972924700782451696644186473100389722973815184405301748249").unwrap()), Fp::get_fp_from_biguint(BigUint::from_str("123488485035126972924700782451696644186473100389722973815184405301748249").unwrap())]);
        let g2_z = Fp2([Fp::get_fp_from_biguint(BigUint::from_str("1").unwrap()), Fp::get_fp_from_biguint(BigUint::from_str("0").unwrap())]);

        let miller_output = miller_loop(g1_x, g1_y, g2_x, g2_y, g2_z);
        let pairing_output = miller_output.final_exponentiate();
        let expected = Fp12::from_str([
                "14915188923217842326587751629532107266878307970218818694751380910709760935829",
                "21623556310676053339817211906609286785561619948753049319824697366480327799543",
                "2836906296597132694225245595765697356003233187879652061016792222014976249577",
                "10009358387570228761033759734219682902521011451682947974354026335988063426477",
                "12817906092968066237117584194400131682501804749830586238732858135104015983083",
                "7786686611664707311556547889601557300361835307451247836157393781910933076023",
                "19482744153990634428187168054080184506672193943515486318298292256286438601300",
                "21242070027891118740874168803249122177395973308657377898849623852850424663235",
                "21289658074295196898147427996706815832652107008933002152032431661843351520416",
                "4347981019511653837656598914020275626117664893317465517086075773641205999465",
                "6341590082023496779372047434473313867272508646860283429158162111150891991928",
                "2822919968093413787714107524913195446612122715915253177262156418079279895532",
        ]);
        assert_eq!(pairing_output, expected);
    }
}
