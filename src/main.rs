use std::io;
use rand::prelude::*;
use num::BigUint;
use num::BigInt;
use num::bigint::RandBigInt;
use num::bigint::Sign;

#[allow(dead_code)]
fn sieve(n: u64) -> Vec<u64> { // generate a vec of u64
    let mut primes = vec![2];

    'outer: for i in 3..n {
        for p in &primes {
            if i % p == 0 {
                continue 'outer;
            }
        }
        primes.push(i);
    }
    primes
}

#[allow(dead_code)]
fn rnum () -> Vec<u8> {
    let mut rng = rand::thread_rng();
    let mut bits = Vec::<u8>::new();
    for _ in 0..1024 {
        if rng.gen::<f32>() > 0.5 {
            bits.push(0);
        }
        else {
            bits.push(1);
        }
    }
    bits[0] = 1;
    bits[1024-1] = 1;
    bits
}

struct BitArray {
    bytes: Vec<u8>,
}
impl BitArray {
    fn new_empty() -> BitArray {
        BitArray { bytes: Vec::<u8>::new() }
    }
    #[allow(dead_code)]
    fn len(&self) -> usize {
        self.bytes.len()
    }
    fn add_byte(&mut self, b: u8) -> () {
        self.bytes.push(b);
    }
    #[allow(dead_code)]
    fn print_bits(&self) -> () {
        for i in 0..self.bytes.len() {
            let mut byte: u8 = self.bytes[i];
            for _ in 0..8 {
                let ch = if byte % 2 == 0 { '0' } else { '1' };
                print!("{}", ch);
                byte /= 2;
            }
        }
        println!();
    }
    fn gen_rand_bits(&mut self, size: u32) {
        let mut rng = rand::thread_rng();
        self.bytes.clear();
        let mut byte: u8 = 0;
        for i in 0..size {
            // Ensure that first and last bits are 1
            if i == 0 || i == size - 1 {
                byte += 1 << i%8;
            }
            else if rng.gen::<f32>() > 0.5 {
                byte += 1 << i%8;
            }
            if i%8 == 7 {
                self.add_byte(byte);
                byte = 0;
            }
        }
        if size%8 != 0 { self.add_byte(byte); }
    }
}

// write n as 2^r*d + 1 with d odd (by factoring out powers of 2 from n - 1);
fn miller_rabin (n: &BigUint, k: u32) -> bool {
    let mut d = n - 1_u32; // m = n - 1
    let mut r: u32 = 0;
    loop {
        if &d % 2_u32 != BigUint::from(0_u32) {
            break;
        }
        d = d / 2_u32;
        r += 1;
    }
    // n = 2^r * d + 1
    //println!("n = {}", n);
    //println!("n = 2^r * d + 1");
    //println!("r = {}", r);
    //println!("d = {}", d);
    assert_eq!(n, &(&d * 2_u32.pow(r) + 1_u32));
    // Witness loop (repeat k times)
    'witness: for _ in 0..k {
        // pick random integer a in range [2, n-2];
        let mut rng = rand::thread_rng();
        let a = rng.gen_biguint_range(&BigUint::from(2_u32), &(n-2_u32));
        //println!("a = {}", a);
        // x = a^d mod n
        let mut x = a.modpow(&d, n);
        if x == BigUint::from(1_u32) || x == n - 1_u32 {
            continue 'witness;
        }
        for _ in 0_u32..(r-1_u32) {
            x = x.modpow(&BigUint::from(2_u32), n);
            if x == n - 1_u32 {
                continue 'witness;
            }
        }
        return false;
    }
    // End Witness loop
    true
}

#[allow(dead_code)]
fn gen_big_prime(primes: &Vec<u64>) -> BigUint {
    let mut bits = BitArray::new_empty();
    loop {
        bits.gen_rand_bits(1024);
        let n = BigUint::from_bytes_le(&bits.bytes);
        //let result = true; // to ommit miller_rabin
        let result = miller_rabin(&n, 64); // worst case error bound: 4^-k
                                           // with k=64, error bound is 1 / 2^128
        if result {
            for p in primes {
                if &n % p == BigUint::from(0_u32) {
                    println!("Failed!!! test with p = {}", p);
                }
            }
            return n;
        }
    }
}

#[allow(dead_code)]
fn extended_gcd(a:i64, b:i64) -> (i64, i64, i64) {
    /* This algorithm can be used to get the
     * multiplicative inverse of a mod b
     * if a and b are coprime
     */
    let mut s0 = 1; let mut s1 = 0;
    let mut t0 = 0; let mut t1 = 1;
    let mut r0 = a; let mut r1 = b;
    while r1 != 0 {
        let quotient = r0 / r1;
        (r0, r1) = (r1, r0 - quotient * r1);
        (s0, s1) = (s1, s0 - quotient * s1);
        (t0, t1) = (t1, t0 - quotient * t1);
    }
    (r0, s0, t0)
}

fn mult_inverse_a_mod_b(a_: &BigUint, b_: &BigUint) -> BigUint
{
    assert!(a_ < b_);
    let a = &biguint_to_bigint(a_);
    let b = &biguint_to_bigint(b_);
    let mut s0 = BigInt::from(1_u32);
    let mut s1 = BigInt::from(0_u32);
    let mut t0 = BigInt::from(0_u32);
    let mut t1 = BigInt::from(1_u32);
    let mut r0 = a + 0_u32;
    let mut r1 = b + 0_u32;
    while &r1 != &BigInt::from(0_u32) {
        let quotient = &r0 / &r1;
        (r0, r1) = (&r1+0_u32, &r0 - &quotient * &r1);
        (s0, s1) = (&s1 + 0_u32, &s0 - &quotient * &s1);
        (t0, t1) = (&t1 + 0_u32, &t0 - &quotient * &t1);
    }
    if s0.sign() == Sign::Minus {
        s0 = &s0 * -(b-BigInt::from(1_u32)) % b;
    }
    bigint_to_biguint(&s0)
}

fn bigint_to_biguint(a: &BigInt) -> BigUint {
    let (sign, bytes) = a.to_bytes_le();
    match sign {
        Sign::Minus => panic!("negative to unsigned!"),
        _ => BigUint::from_bytes_le(&bytes),
    }
}
fn biguint_to_bigint(a: &BigUint) -> BigInt {
    BigInt::from_bytes_le(Sign::Plus, &a.to_bytes_le())
}

fn encrypt(m: &BigUint, e: &BigUint, n: &BigUint) -> BigUint {
    m.modpow(e, n)
}

fn decrypt(c: &BigUint, d: &BigUint, n: &BigUint) -> BigUint {
    c.modpow(d, n)
}

fn main() {
    println!("Enter a message to be encrypted: ");
    let mut input = String::new();
    io::stdin()
        .read_line(&mut input)
        .expect("Failed to read line");

    let m = BigUint::from_bytes_le(input.as_bytes());
    println!("string encoded as:\n{}", m);

    println!("\ngenrating first few primes...");
    let primes = sieve(200_000);
    println!("generating p...");
    let p = gen_big_prime(&primes);
    println!("generating q...");
    let q = gen_big_prime(&primes);
    let phi = (&p - 1_u32)*(&q - 1_u32);
    let n = &p * &q;
    let e = BigUint::from(primes[primes.len()-1]);
    let d = mult_inverse_a_mod_b(&e, &phi);

    println!("\nPublic key:\n{}|{}", e, n);
    println!("\nPrivate key:\n{}\n", d);

    let c = encrypt(&m, &e, &n);
    println!("string encrypted as:\n{}", &c);
    let bytes = decrypt(&c, &d, &n).to_bytes_le();
    match std::str::from_utf8(&bytes) {
        Ok(v) => println!("\nstring decrypted as:\n{}", v),
        Err(e) => panic!("Invalid sequence {}", e),
    };

}
