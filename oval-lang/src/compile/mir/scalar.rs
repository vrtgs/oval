use crate::compile::mir::IntTy;
use core::fmt::{Display, Formatter};

#[derive(Debug, Copy, Clone)]
pub struct Scalar {
    value: u64
}

#[derive(Debug, thiserror::Error)]
#[error("out of range integral type conversion attempted")]
pub struct ParseIntLiteralError(());

impl ParseIntLiteralError {
    pub(crate) const NEW: Self = Self(());
}

impl From<core::num::TryFromIntError> for ParseIntLiteralError {
    fn from(_: core::num::TryFromIntError) -> Self {
        Self::NEW
    }
}

#[derive(Debug, thiserror::Error)]
pub enum DivideError {
    #[error("attempted to divide by zero")]
    DivideByZero,
    #[error("attempted to divide with overflow")]
    Overflow,
}

impl Scalar {
    pub const fn from_bool(value: bool) -> Self {
        Self {
            value: value as u64
        }
    }

    pub const TRUE: Scalar = Scalar::from_bool(true);
    pub const FALSE: Scalar = Scalar::from_bool(false);

    pub const fn parse_int_literal(negative: bool, value: u128, int: IntTy) -> Result<Self, ParseIntLiteralError> {
        if (value > u64::MAX as u128) || (negative && !int.is_signed()) {
            return Err(ParseIntLiteralError::NEW)
        }

        let mut value = value as u64;

        if negative {
            if value > const { i64::MIN.unsigned_abs() } {
                return Err(ParseIntLiteralError::NEW)
            }
            value = value.wrapping_neg();
        } else if let IntTy::I64 = int && value > i64::MAX.cast_unsigned() {
            return Err(ParseIntLiteralError::NEW)
        }

        if value != int.mask(value) {
            return Err(ParseIntLiteralError::NEW)
        }

        Ok(Self { value })
    }
}

#[allow(unused_macros, reason="if this does get used; it means the program isn't compiling")]
macro_rules! sign_err {
    ($sign_name: ident) => {
        compile_error!(concat!("unknown sign ty ", stringify!($sign_name), "; expected agnostic or aware"))
    };
}

macro_rules! impl_overflowing_op {
    (agnostic; $overflowing_name: ident $method_name: ident) => {
        impl_overflowing_op!(aware; $overflowing_name $method_name);
    };
    (aware; $overflowing_name: ident $method_name: ident) => {
        #[inline]
        pub const fn $method_name(self, other: Self, int: IntTy) -> (Self, bool) {
            self.assert_canon(int);
            other.assert_canon(int);

            let (this, other) = (self.value, other.value);

            let (unsigned, unsigned_flag) = u64::$overflowing_name(this, other);
            let (signed, signed_flag) = i64::$overflowing_name(this.cast_signed(), other.cast_signed());

            let value = int.select_masked(unsigned, signed);
            let overflowed = int.select_bool(
                (value != unsigned) | unsigned_flag,
                (value != signed.cast_unsigned()) | signed_flag
            );
            (Self { value }, overflowed)
        }
    };
    ($sign_name: ident; $_: ident $__: ident) => {
        sign_err!($sign_name)
    }
}
macro_rules! impl_wrapping_op {
    (agnostic; $wrapping_name: ident $method_name: ident) => {
        #[inline(always)]
        pub const fn $method_name(self, other: Self, int: IntTy) -> Self {
            self.assert_canon(int);
            other.assert_canon(int);

            let (this, other) = (self.value, other.value);
            Self { value: int.mask(u64::$wrapping_name(this, other)) }
        }
    };
    (aware; $wrapping_name: ident $method_name: ident) => {
        #[inline]
        pub const fn $method_name(self, other: Self, int: IntTy) -> Self {
            self.assert_cannon(int);
            other.assert_cannon(int);

            let (this, other) = (self.value, other.value);
            let unsigned = u64::$wrapping_name(this, other);
            let signed = i64::$wrapping_name(this.cast_signed(), other.cast_signed());
            Self { value: int.select_masked(unsigned, signed) }
        }
    };
    ($sign_name: ident; $_: ident $__: ident) => {
        sign_err!($sign_name)
    }
}


// FIXME core::hint::cold_path
#[cold]
#[inline(always)]
const fn cold_path() {}

macro_rules! impl_arithmetic_binop {
    ($(
        name: $name: ident, sign $sign_ty: ident;
    )+) => {
        pastey::paste! {$(
            impl_overflowing_op!($sign_ty; [<overflowing_ $name>] [<overflowing_i $name>]);
            impl_wrapping_op!($sign_ty; [<wrapping_ $name>] [<i $name>]);

            #[inline]
            pub const fn [<checked_i $name>](self, other: Self, int: IntTy) -> Option<Self> {
                let (new, overflow) = self.[<overflowing_i $name>](other, int);
                if overflow {
                    cold_path();
                    return None
                }
                Some(new)
            }
        )+}
    };
}

macro_rules! impl_divide_like {
    ($(
        name: $name: ident, sign aware;
    )+) => {
        pastey::paste! {$(
            #[inline(always)]
            pub const fn [<i $name>](self, other: Self, int: IntTy) -> Result<Self, DivideError> {
                let (this, other) = (self.value, other.value);
                if other == 0 {
                    cold_path();
                    return Err(DivideError::DivideByZero)
                }

                // division is slow enough that branching is cheaper
                let value = match int.is_signed() {
                    true => {
                        let (signed, overflowed_i64)
                            = i64::[<overflowing_ $name>](this.cast_signed(), other.cast_signed());
                        let val = signed.cast_unsigned();
                        if (int.mask(val) != val) | overflowed_i64 {
                            cold_path();
                            return Err(DivideError::Overflow)
                        }
                        val
                    }
                    false => unsafe {
                        u64::[<checked_ $name>](this, other).unwrap_unchecked()
                    },
                };

                Ok(Self { value })
            }
        )+}
    };
}

macro_rules! impl_bitwise_binop {
    ($($name: ident, $op: tt;)+) => {
        $(#[inline(always)]
        pub const fn $name(self, other: Self, int: IntTy) -> Self {
            self.assert_canon(int);
            other.assert_canon(int);

            let (this, other) = (self.value, other.value);
            let _ = int;
            Self { value: this $op other }
        })+
    };
}


macro_rules! impl_icmp_inner {
    ($real_name: ident, $op: tt) => {
        #[inline(always)]
        pub const fn $real_name(self, other: Self, int: IntTy) -> bool {
            let (this, other) = (self.value, other.value);
            let (s_this, s_other) = (this.cast_signed(), other.cast_signed());
            int.select_bool(this $op other, s_this $op s_other)
        }
    };
}

macro_rules! impl_icmp {
    ($($name: ident, $op: tt;)+) => {
        pastey::paste! {$( impl_icmp_inner!([<i $name>], $op); )+}
    };
}

impl Scalar {
    #[inline(always)]
    const fn assert_canon(self, int: IntTy) {
        debug_assert!(self.value == int.mask(self.value))
    }

    impl_arithmetic_binop!(
        /* this is only true since signed types are represented in a fully wide two's compliment */
        name: add, sign agnostic;
        name: sub, sign agnostic;
        name: mul, sign agnostic;
    );

    impl_divide_like!(
        name: div, sign aware;
        name: rem, sign aware;
    );


    impl_bitwise_binop!(
        bitand, &;
        bitxor, ^;
        bitor,  |;
    );

    pub const fn bitnot(self, int: IntTy) -> Self {
        self.assert_canon(int);
        Self { value: int.mask(!self.value) }
    }

    #[inline(always)]
    pub const fn ieq(self, other: Self, int: IntTy) -> bool {
        self.assert_canon(int);
        other.assert_canon(int);
        self.value == other.value
    }

    #[inline(always)]
    pub const fn ine(self, other: Self, int: IntTy) -> bool {
        self.assert_canon(int);
        other.assert_canon(int);
        self.value != other.value
    }

    impl_icmp!(
        lt, <;
        gt, >;
        le, <=;
        ge, >=;
    );

    pub const fn icast(self, from: IntTy, to: IntTy) -> Self {
        self.assert_canon(from);
        // `self.value` is already in the canonical representation for `from`.
        // Integer casts are equivalent to truncating to the destination width and
        // then (if signed) sign-extending — exactly what `to.mask` does.
        Self { value: to.mask(self.value) }
    }

    pub const fn idisplay(self, int_ty: IntTy) -> impl Display {
        self.assert_canon(int_ty);

        struct IntDisplay {
            scalar: Scalar,
            ty: IntTy
        }

        impl Display for IntDisplay {
            fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
                let val = self.scalar.value;
                match self.ty.is_signed() {
                    true => <i64 as Display>::fmt(&val.cast_signed(), f),
                    false => <u64 as Display>::fmt(&val, f),
                }
            }
        }

        IntDisplay {
            scalar: self,
            ty: int_ty
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::format;

    #[test]
    fn mask_unsigned_truncates() {
        assert_eq!(IntTy::U8.mask(0), 0);
        assert_eq!(IntTy::U8.mask(255), 255);
        assert_eq!(IntTy::U8.mask(256), 0);
        assert_eq!(IntTy::U8.mask(0x1FF), 0xFF);

        assert_eq!(IntTy::U16.mask(0x1_0000), 0);
        assert_eq!(IntTy::U16.mask(0x12345), 0x2345);
    }

    #[test]
    fn mask_signed_sign_extends_and_truncates() {
        // I8 canonical forms:
        //  127  -> 0x000...007F
        // -128  -> 0xFFF...FF80
        //   -1  -> 0xFFF...FFFF
        assert_eq!(IntTy::I8.mask(0x7F), 0x7F);
        assert_eq!(IntTy::I8.mask(0x80), (!0u64) << 7); // 0x...FF80
        assert_eq!(IntTy::I8.mask(0xFF), !0u64);

        // Values with extra high bits should first truncate to 8 bits then sign-extend.
        assert_eq!(IntTy::I8.mask(0x1FF), !0u64); // trunc to 0xFF == -1
        assert_eq!(IntTy::I8.mask(0x180), (!0u64) << 7); // trunc to 0x80 == -128

        // I16 spot-check
        assert_eq!(IntTy::I16.mask(0x7FFF), 0x7FFF);
        assert_eq!(IntTy::I16.mask(0x8000), (!0u64) << 15);
        assert_eq!(IntTy::I16.mask(0xFFFF), !0u64);
    }

    #[test]
    fn parse_int_literal_rejects_out_of_range_and_sign_mismatch() {
        // negative into unsigned is rejected
        assert!(Scalar::parse_int_literal(true, 1, IntTy::U8).is_err());

        // u128 that doesn't fit u64 is rejected
        assert!(Scalar::parse_int_literal(false, u64::MAX as u128 + 1, IntTy::U64).is_err());

        // I8 bounds: [-128, 127]
        assert!(Scalar::parse_int_literal(false, 128, IntTy::I8).is_err());
        assert!(Scalar::parse_int_literal(true, 129, IntTy::I8).is_err());

        // U8 bounds: [0, 255]
        assert!(Scalar::parse_int_literal(false, 256, IntTy::U8).is_err());

        // I64 special-case: positive > i64::MAX rejected
        assert!(Scalar::parse_int_literal(false, (i64::MAX as u128) + 1, IntTy::I64).is_err());
    }

    #[test]
    fn parse_int_literal_accepts_and_canonicalizes() {
        // U8 255 ok
        let s = Scalar::parse_int_literal(false, 255, IntTy::U8).unwrap();
        assert_eq!(s.value, 255);

        // I8 -1 canonicalizes to all-ones u64
        let s = Scalar::parse_int_literal(true, 1, IntTy::I8).unwrap();
        assert_eq!(s.value, !0u64);

        // I8 -128 canonicalizes to sign-extended form
        let s = Scalar::parse_int_literal(true, 128, IntTy::I8).unwrap();
        assert_eq!(s.value, (!0u64) << 7);
    }

    #[test]
    fn checked_and_wrapping_add_unsigned() {
        let a = Scalar { value: 250 };
        let b = Scalar { value: 10 };

        // wrapping within U8: 250 + 10 = 260 -> 4
        let w = a.iadd(b, IntTy::U8);
        assert_eq!(w.value, 4);

        // checked should detect overflow
        assert!(a.checked_iadd(b, IntTy::U8).is_none());

        // overflowing reports overflow
        let (o, overflowed) = a.overflowing_iadd(b, IntTy::U8);
        assert_eq!(o.value, 4);
        assert!(overflowed);
    }

    #[test]
    fn checked_and_wrapping_add_signed() {
        // 120 + 10 overflows i8 (max 127)
        let a = Scalar { value: IntTy::I8.mask(120) };
        let b = Scalar { value: IntTy::I8.mask(10) };

        assert!(a.checked_iadd(b, IntTy::I8).is_none());

        // wrapping i8: 120 + 10 = 130 -> -126
        let w = a.iadd(b, IntTy::I8);
        assert_eq!(w.value, IntTy::I8.mask(130)); // trunc to 0x82 and sign-extend

        let (o, overflowed) = a.overflowing_iadd(b, IntTy::I8);
        assert_eq!(o.value, w.value);
        assert!(overflowed);
    }

    #[test]
    fn divide_errors_and_signed_overflow_case() {
        let one_u8 = Scalar { value: 1 };
        let zero = Scalar { value: 0 };

        assert!(matches!(
            one_u8.idiv(zero, IntTy::U8),
            Err(DivideError::DivideByZero)
        ));

        // i8 MIN / -1 overflows
        let min_i8 = Scalar { value: IntTy::I8.mask(0x80) }; // -128 canonical
        let neg_one = Scalar { value: !0u64 }; // -1 canonical
        assert!(matches!(
            min_i8.idiv(neg_one, IntTy::I8),
            Err(DivideError::Overflow)
        ));
    }

    #[test]
    fn comparisons_respect_signedness() {
        // Signed: -1 < 1
        let neg_one = Scalar { value: IntTy::I8.mask((-1_i64).cast_unsigned()) };
        let one_i8 = Scalar { value: IntTy::I8.mask(1) };
        assert!(neg_one.ilt(one_i8, IntTy::I8));
        assert!(one_i8.igt(neg_one, IntTy::I8));

        // Unsigned: 255 > 1
        let u255 = Scalar { value: 255 };
        let u1 = Scalar { value: 1 };
        assert!(u255.igt(u1, IntTy::U8));
        assert!(u1.ilt(u255, IntTy::U8));
    }

    #[test]
    fn display_formats_as_signed_or_unsigned() {
        let neg_one = Scalar { value: !0u64 };
        assert_eq!(format!("{}", neg_one.idisplay(IntTy::I8)), "-1");

        let u255 = Scalar { value: 255 };
        assert_eq!(format!("{}", u255.idisplay(IntTy::U8)), "255");
    }

    #[test]
    fn bitnot_is_masked() {
        let x = Scalar { value: 0b0000_1111 };
        let y = x.bitnot(IntTy::U8);
        // !0b00001111 within U8 => 0b11110000 == 240
        assert_eq!(y.value, 0b1111_0000);
    }

    #[test]
    fn icast_matches_integer_cast_semantics() {
        // i8(-1) -> u16 == 65535
        let m1_i8 = Scalar { value: IntTy::I8.mask((-1_i64).cast_unsigned()) };
        let as_u16 = m1_i8.icast(IntTy::I8, IntTy::U16);
        assert_eq!(as_u16.value, 0xFFFF);

        // u8(255) -> i8 == -1 (canonical all-ones)
        let u255 = Scalar { value: IntTy::U8.mask(255) };
        let as_i8 = u255.icast(IntTy::U8, IntTy::I8);
        assert_eq!(as_i8.value, !0u64);

        // u16(0x1234) -> u8 == 0x34
        let u16v = Scalar { value: IntTy::U16.mask(0x1234) };
        let as_u8 = u16v.icast(IntTy::U16, IntTy::U8);
        assert_eq!(as_u8.value, 0x34);

        // i8(-128) -> i16 stays -128 (sign-extended canonical)
        let min_i8 = Scalar { value: IntTy::I8.mask(0x80) }; // -128 canonical
        let as_i16 = min_i8.icast(IntTy::I8, IntTy::I16);
        assert_eq!(as_i16.value, IntTy::I16.mask(0xFF80));

        // i16(-1) -> u8 == 255
        let m1_i16 = Scalar { value: IntTy::I16.mask((-1_i64).cast_unsigned()) };
        let as_u8_2 = m1_i16.icast(IntTy::I16, IntTy::U8);
        assert_eq!(as_u8_2.value, 255);

        // widening unsigned preserves value
        let u8v = Scalar { value: IntTy::U8.mask(200) };
        let as_u64 = u8v.icast(IntTy::U8, IntTy::U64);
        assert_eq!(as_u64.value, 200);
    }

    #[test]
    fn icast_result_is_canonical_for_destination() {
        let x = Scalar { value: IntTy::U16.mask(0xFF80) }; // 65408
        let y = x.icast(IntTy::U16, IntTy::I8);           // trunc to 0x80 => -128
        assert_eq!(y.value, IntTy::I8.mask(0x80));
    }
}
