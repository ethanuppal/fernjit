pub mod bit_manip;

use std::fmt;

use static_assertions::const_assert;

#[derive(Debug)]
pub struct NaNBox {
    value: f64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NaNBoxType {
    Double,
    Int,
    Pointer,
}

impl fmt::Display for NaNBoxType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Double => write!(f, "double"),
            Self::Int => write!(f, "int"),
            Self::Pointer => write!(f, "pointer"),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IntegerWontFitError(i64);

impl fmt::Display for IntegerWontFitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} is not in the range [{}, {}] and won't fit in a NaNBox",
            self.0,
            -2i64.pow(DATA_BITS - 1),
            2i64.pow(DATA_BITS - 1) - 1
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub struct IncorrectTypeError {
    expected: NaNBoxType,
    actual: NaNBoxType,
}

impl fmt::Display for IncorrectTypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "expected NaNBox to store {} but got {}",
            self.expected, self.actual
        )
    }
}

const DATA_MASK: u64 = 0x000_3_FFFF_FFFF_FFFF;
const IS_BOXED_PATTERN: u64 = 0x7FF_C_0000_0000_0000;
const TYPE_INT_PATTERN: u64 = 0x800_0_0000_0000_0000;
const TYPE_PTR_PATTERN: u64 = 0x000_0_0000_0000_0000;

const DATA_BITS: u32 = DATA_MASK.trailing_ones();

const ACTUAL_NAN: f64 = f64::from_bits(0x7FF_8_0000_0000_0000);
const_assert!(ACTUAL_NAN.is_nan());

impl NaNBox {
    pub fn stored_type(&self) -> NaNBoxType {
        let bits = self.value.to_bits();
        if bits & IS_BOXED_PATTERN != IS_BOXED_PATTERN {
            return NaNBoxType::Double;
        }

        if bits & TYPE_INT_PATTERN == TYPE_INT_PATTERN {
            NaNBoxType::Int
        } else {
            NaNBoxType::Pointer
        }
    }
}

impl From<f64> for NaNBox {
    fn from(value: f64) -> Self {
        return NaNBox {
            value: if value.is_nan() { ACTUAL_NAN } else { value },
        };
    }
}

impl TryFrom<i64> for NaNBox {
    type Error = IntegerWontFitError;

    fn try_from(value: i64) -> Result<Self, Self::Error> {
        if value < 0 && value.leading_ones() <= i64::BITS - DATA_BITS {
            return Err(IntegerWontFitError(value));
        }

        if value > 0 && value.leading_zeros() <= i64::BITS - DATA_BITS {
            return Err(IntegerWontFitError(value));
        }

        return Ok(NaNBox {
            value: f64::from_bits(
                IS_BOXED_PATTERN
                    | TYPE_INT_PATTERN
                    | (DATA_MASK & (value as u64)),
            ),
        });
    }
}

impl TryFrom<NaNBox> for f64 {
    type Error = IncorrectTypeError;

    fn try_from(value: NaNBox) -> Result<Self, Self::Error> {
        let value_type = value.stored_type();
        if value_type == NaNBoxType::Double {
            Ok(value.value)
        } else {
            Err(IncorrectTypeError {
                expected: NaNBoxType::Double,
                actual: value_type,
            })
        }
    }
}

impl TryFrom<NaNBox> for i64 {
    type Error = IncorrectTypeError;

    fn try_from(value: NaNBox) -> Result<Self, Self::Error> {
        let value_type = value.stored_type();

        if value_type == NaNBoxType::Int {
            let bits = value.value.to_bits();

            let sign_extended: u64 =
                bit_manip::sign_extend_to(bits & DATA_MASK, DATA_BITS);

            Ok(sign_extended as i64)
        } else {
            Err(IncorrectTypeError {
                expected: NaNBoxType::Int,
                actual: value_type,
            })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_f64_conversion() {
        let original_f64 = 3.14159;
        let nan_box = NaNBox::from(original_f64);
        assert_eq!(nan_box.stored_type(), NaNBoxType::Double);
        let converted_f64: f64 = nan_box.try_into().unwrap();
        assert_eq!(original_f64, converted_f64);

        let nan_f64 = f64::NAN;
        let nan_box_nan = NaNBox::from(nan_f64);
        assert_eq!(nan_box_nan.stored_type(), NaNBoxType::Double);
        let converted_nan: f64 = nan_box_nan.try_into().unwrap();
        assert!(converted_nan.is_nan());
    }

    #[test]
    fn test_i64_conversion() {
        let original_i64 = 123456789012345i64;
        let nan_box = NaNBox::try_from(original_i64).unwrap();
        assert_eq!(nan_box.stored_type(), NaNBoxType::Int);
        let converted_i64: i64 = nan_box.try_into().unwrap();
        assert_eq!(original_i64, converted_i64);

        let negative_i64 = -98765432109876i64;
        let nan_box_neg = NaNBox::try_from(negative_i64).unwrap();
        assert_eq!(nan_box_neg.stored_type(), NaNBoxType::Int);
        let converted_neg_i64: i64 = nan_box_neg.try_into().unwrap();
        assert_eq!(negative_i64, converted_neg_i64);
    }

    #[test]
    fn test_i64_conversion_limits() {
        let original_i64 = 2i64.pow(DATA_BITS - 1) - 1;
        let nan_box = NaNBox::try_from(original_i64).unwrap();
        assert_eq!(nan_box.stored_type(), NaNBoxType::Int);
        let converted_i64: i64 = nan_box.try_into().unwrap();
        assert_eq!(original_i64, converted_i64);

        let negative_i64 = -2i64.pow(DATA_BITS - 1);
        let nan_box_neg = NaNBox::try_from(negative_i64).unwrap();
        assert_eq!(nan_box_neg.stored_type(), NaNBoxType::Int);
        let converted_neg_i64: i64 = nan_box_neg.try_into().unwrap();
        assert_eq!(negative_i64, converted_neg_i64);
    }

    #[test]
    fn test_i64_wont_fit() {
        // Test a value that is too large to fit
        let too_large_pos = 2i64.pow(DATA_BITS - 1);
        let result = NaNBox::try_from(too_large_pos);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().0, too_large_pos);

        // Test a value that is too small (negative) to fit
        let too_small_neg = -2i64.pow(DATA_BITS - 1) - 1;
        let result = NaNBox::try_from(too_small_neg);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err().0, too_small_neg);
    }

    #[test]
    fn test_incorrect_type() {
        let double_box = NaNBox::from(1.23);
        let result: Result<i64, IncorrectTypeError> = double_box.try_into();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.expected, NaNBoxType::Int);
        assert_eq!(err.actual, NaNBoxType::Double);

        let int_box = NaNBox::try_from(123i64).unwrap();
        let result: Result<f64, IncorrectTypeError> = int_box.try_into();
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert_eq!(err.expected, NaNBoxType::Double);
        assert_eq!(err.actual, NaNBoxType::Int);
    }
}
