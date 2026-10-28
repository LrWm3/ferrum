//! Upstream:
//! https://github.com/viperproject/silver/blob/c4f54b84703a04434b03e97bfea87dbd09870fd2/src/main/scala/viper/silver/utility/Common.scala
//!
//! Purpose:
//! Provide structural equality, file writing and exact rational arithmetic.
//!
//! Planned Rust structure:
//! Port StructuralEquality and generateHashCode, toFile/PrintWriter, Rational and zero/one
//! constructors.
//!
//! Behavior to preserve:
//! Equality checks runtime type and defining members; hash folds by 41. Rational rejects zero
//! denominator, normalizes by gcd with positive denominator, and supports exact
//! arithmetic/comparison. Upstream hash uses original n,d despite normalized equality: preserve
//! or document a deliberate fix. File writer creates parents and supports append/autoflush.
//!
//! Integration:
//! Shared by Silver and downstream utility clients; rational consumers must agree on arithmetic.
//!
//! Rust adaptations:
//! Follow porting/conventions.md for shared ownership, errors and collection semantics; native
//! runtime substitutions remain provisional.
//!
//! Open decisions:
//! Resolve Rational hash/equality mismatch and runtime-specific hash compatibility with
//! consumers.
//!
//! Status: partially implemented; structural equality integration with concrete types remains.

// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{Signed, Zero};
use std::cmp::Ordering;
use std::fmt;
use std::fs::{self, OpenOptions};
use std::io::{self, BufWriter, Write};
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::path::Path;

/// The Scala fold over already-computed member hashes, with wrapping Int arithmetic.
pub fn generate_hash_code(hashes: impl IntoIterator<Item = i32>) -> i32 {
    hashes
        .into_iter()
        .fold(0i32, |code, hash| code.wrapping_mul(41).wrapping_add(hash))
}

/// A type's equality-defining members, used with its native `Eq` and `Hash` implementations.
pub trait StructuralEquality {
    type Members: PartialEq;
    fn equality_defining_members(&self) -> Self::Members;
}

/// Compare the defining members of values of the same concrete Rust type.
pub fn structural_equals<T: StructuralEquality>(left: &T, right: &T) -> bool {
    std::ptr::eq(left, right)
        || left.equality_defining_members() == right.equality_defining_members()
}

pub fn to_file(contents: &str, file: impl AsRef<Path>) -> io::Result<()> {
    let mut sink = print_writer(file, true, false)?;
    sink.write_all(contents.as_bytes())?;
    sink.flush()
}

/// Buffered writer whose line-writing operation honors Java PrintWriter's auto-flush setting.
pub struct PrintWriter {
    sink: BufWriter<fs::File>,
    auto_flush: bool,
}
impl PrintWriter {
    pub fn println(&mut self, line: &str) -> io::Result<()> {
        writeln!(self.sink, "{line}")?;
        if self.auto_flush {
            self.sink.flush()?;
        }
        Ok(())
    }
}
impl Write for PrintWriter {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.sink.write(bytes)
    }
    fn flush(&mut self) -> io::Result<()> {
        self.sink.flush()
    }
}

pub fn print_writer(
    file: impl AsRef<Path>,
    auto_flush: bool,
    append: bool,
) -> io::Result<PrintWriter> {
    let file = file.as_ref();
    if let Some(parent) = file.parent().filter(|p| !p.as_os_str().is_empty()) {
        fs::create_dir_all(parent)?;
    }
    let sink = OpenOptions::new()
        .create(true)
        .write(true)
        .append(append)
        .truncate(!append)
        .open(file)?;
    Ok(PrintWriter {
        sink: BufWriter::new(sink),
        auto_flush,
    })
}

/// Reduced exact rational; equality and hashing both use the reduced representation.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Rational(BigRational);
impl Rational {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Self {
        assert!(
            !denominator.is_zero(),
            "Denominator of Rational must not be 0."
        );
        Self(BigRational::new(numerator, denominator))
    }
    pub fn numerator(&self) -> &BigInt {
        self.0.numer()
    }
    pub fn denominator(&self) -> &BigInt {
        self.0.denom()
    }
    pub fn zero() -> Self {
        Self::new(0.into(), 1.into())
    }
    pub fn one() -> Self {
        Self::new(1.into(), 1.into())
    }
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }
    pub fn signum(&self) -> Self {
        Self(self.0.signum())
    }
    pub fn inverse(&self) -> Self {
        Self::new(self.denominator().clone(), self.numerator().clone())
    }
    pub fn compare(&self, other: &Self) -> Ordering {
        self.cmp(other)
    }
}
impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}/{}", self.numerator(), self.denominator())
    }
}
impl Add for Rational {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        Self(self.0 + other.0)
    }
}
impl Sub for Rational {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        Self(self.0 - other.0)
    }
}
impl Mul for Rational {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        Self(self.0 * other.0)
    }
}
impl Div for Rational {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        self * other.inverse()
    }
}
impl Neg for Rational {
    type Output = Self;
    fn neg(self) -> Self {
        Self(-self.0)
    }
}
