use crate::{
    // gadgets::unsigned::{
    //     add::{Diff, Sum},
    //     mul::Product,
    // },
    lair::chipset::Chipset,
    lurk::zstore::DIGEST_SIZE,
};

/// Performs efficient bit checking to know whether an `i64` is within `i63` range.
#[inline]
pub fn is_within_i63_range(i: i64) -> bool {
    let top_two_bits = (i >> 62) & 0b11;
    //          positive || negative
    top_two_bits == 0b00 || top_two_bits == 0b11
}

/// Wrapper to represent signed integers of 63 bits.
/// It uses an `i64` internally that's assumed to have the MSBit set to 0.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct I63(i64);

impl I63 {
    #[inline]
    pub fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }

    #[inline]
    pub fn from_le_bytes(bytes: [u8; 8]) -> Self {
        Self(i64::from_le_bytes(bytes))
    }
}

impl From<i64> for I63 {
    #[inline]
    fn from(i: i64) -> Self {
        // perform an `and` with `MAX_U63`
        Self(i & 9223372036854775807)
    }
}

impl From<I63> for i64 {
    #[inline]
    fn from(i: I63) -> Self {
        // left shift to remove the sign bit and shift right to restore the i64 sign
        (i.0 << 1) >> 1
    }
}

impl std::fmt::Display for I63 {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", i64::from(*self))
    }
}

// type Sum63<T> = Sum<T, 8, 127>;
// type Diff63<T> = Diff<T, 8, 127>;
// type Product63<T> = Product<T, 8, 127>;

/// Gadgets for operations over `I63`, assumed to be encoded in two's complement
#[derive(Clone)]
pub enum I63Gadgets {
    Add,
    Sub,
    Mul,
    IntoSignAbs,
    FromSignAbs,
}

impl<F> Chipset<F> for I63Gadgets {
    fn input_size(&self) -> usize {
        match self {
            Self::Add | Self::Sub | Self::Mul => 2 * DIGEST_SIZE,
            Self::IntoSignAbs => DIGEST_SIZE,
            Self::FromSignAbs => 1 + DIGEST_SIZE,
        }
    }

    fn output_size(&self) -> usize {
        match self {
            Self::Add | Self::Sub | Self::Mul | Self::FromSignAbs => DIGEST_SIZE,
            Self::IntoSignAbs => 1 + DIGEST_SIZE,
        }
    }

    fn witness_size(&self) -> usize {
        todo!()
    }

    fn require_size(&self) -> usize {
        todo!()
    }

    fn execute_simple(&self, _input: &[F]) -> Vec<F> {
        todo!()
    }

    fn populate_witness(&self, _input: &[F], _witness: &mut [F]) -> Vec<F> {
        todo!()
    }

    fn eval<AB: p3_air::AirBuilder<F = F> + crate::air::builder::LookupBuilder>(
        &self,
        _builder: &mut AB,
        _is_real: AB::Expr,
        _input: Vec<AB::Expr>,
        _witness: &[AB::Var],
        _nonce: AB::Expr,
        _requires: &[crate::air::builder::RequireRecord<AB::Var>],
    ) -> Vec<AB::Expr> {
        todo!()
    }
}

#[cfg(test)]
mod test {
    use super::{is_within_i63_range, I63};

    const MIN_I63: i64 = -4611686018427387904;
    const MAX_I63: i64 = 4611686018427387903;

    #[test]
    fn test_is_within_i63_range() {
        let cases = [
            (MIN_I63 - 2, false),
            (MIN_I63 - 1, false),
            (MIN_I63, true),
            (MIN_I63 + 1, true),
            (MIN_I63 / 2, true),
            (-1, true),
            (0, true),
            (1, true),
            (MAX_I63 / 2, true),
            (MAX_I63 - 1, true),
            (MAX_I63, true),
            (MAX_I63 + 1, false),
            (MAX_I63 + 2, false),
        ];
        for (i, expected) in cases {
            assert_eq!(is_within_i63_range(i), expected);
        }
    }

    #[test]
    fn test_i63_roundtrip() {
        let cases = [
            MIN_I63,
            MIN_I63 + 1,
            MIN_I63 / 2,
            -1,
            0,
            1,
            MAX_I63 / 2,
            MAX_I63 - 1,
            MAX_I63,
        ];
        for i in cases {
            let i63: I63 = i.into();
            let bytes = i63.to_le_bytes();
            assert_eq!(i63, I63::from_le_bytes(bytes));
            assert_eq!(i, i63.into());
        }
    }
}
