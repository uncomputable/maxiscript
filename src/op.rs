use std::fmt;
use std::str::FromStr;

use bitcoin::opcodes;

/// A Bitcoin Script operation that is a builtin function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Operation(opcodes::Opcode);

impl std::hash::Hash for Operation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u8(self.0.to_u8());
    }
}

impl FromStr for Operation {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let ret = match s {
            // Flow control
            "verify" => Self(opcodes::all::OP_VERIFY),

            // Bitwise logic
            "equal" => Self(opcodes::all::OP_EQUAL),
            "equal_verify" => Self(opcodes::all::OP_EQUALVERIFY),

            // Arithmetic
            "one_add" => Self(opcodes::all::OP_1ADD),
            "one_sub" => Self(opcodes::all::OP_1SUB),
            "negate" => Self(opcodes::all::OP_NEGATE),
            "abs" => Self(opcodes::all::OP_ABS),
            "not" => Self(opcodes::all::OP_NOT),
            "zero_not_equal" => Self(opcodes::all::OP_0NOTEQUAL),
            "add" => Self(opcodes::all::OP_ADD),
            "sub" => Self(opcodes::all::OP_SUB),
            "bool_and" => Self(opcodes::all::OP_BOOLAND),
            "bool_or" => Self(opcodes::all::OP_BOOLOR),
            "num_equal" => Self(opcodes::all::OP_NUMEQUAL),
            "num_equal_verify" => Self(opcodes::all::OP_NUMEQUALVERIFY),
            "num_not_equal" => Self(opcodes::all::OP_NUMNOTEQUAL),
            "less_than" => Self(opcodes::all::OP_LESSTHAN),
            "greater_than" => Self(opcodes::all::OP_GREATERTHAN),
            "less_than_or_equal" => Self(opcodes::all::OP_LESSTHANOREQUAL),
            "greater_than_or_equal" => Self(opcodes::all::OP_GREATERTHANOREQUAL),
            "min" => Self(opcodes::all::OP_MIN),
            "max" => Self(opcodes::all::OP_MAX),
            "within" => Self(opcodes::all::OP_WITHIN),

            // Crypto
            "ripemd160" => Self(opcodes::all::OP_RIPEMD160),
            "sha1" => Self(opcodes::all::OP_SHA1),
            "sha256" => Self(opcodes::all::OP_SHA256),
            "hash160" => Self(opcodes::all::OP_HASH160),
            "hash256" => Self(opcodes::all::OP_HASH256),
            "checksig" => Self(opcodes::all::OP_CHECKSIG),
            "checksig_verify" => Self(opcodes::all::OP_CHECKSIGVERIFY),
            // Multisig operations are disabled in Tapscript
            // "checkmultisig" => Self(opcodes::all::OP_CHECKMULTISIG),
            // "checkmultisigverify" => Self(opcodes::all::OP_CHECKMULTISIGVERIFY),
            "checksig_add" => Self(opcodes::all::OP_CHECKSIGADD),

            // Locktime
            "check_locktime_verify" => Self(opcodes::all::OP_CLTV),
            "check_sequence_verify" => Self(opcodes::all::OP_CSV),
            _ => return Err(()),
        };
        Ok(ret)
    }
}

impl Operation {
    /// Returns the number of arguments that this operation takes as input.
    pub const fn n_args(self) -> usize {
        match self.0 {
            // Flow control
            opcodes::all::OP_VERIFY => 1,

            // Bitwise logic
            opcodes::all::OP_EQUAL => 2,
            opcodes::all::OP_EQUALVERIFY => 2,

            // Arithmetic
            opcodes::all::OP_1ADD => 1,
            opcodes::all::OP_1SUB => 1,
            opcodes::all::OP_NEGATE => 1,
            opcodes::all::OP_ABS => 1,
            opcodes::all::OP_NOT => 1,
            opcodes::all::OP_0NOTEQUAL => 1,
            opcodes::all::OP_ADD => 2,
            opcodes::all::OP_SUB => 2,
            opcodes::all::OP_BOOLAND => 2,
            opcodes::all::OP_BOOLOR => 2,
            opcodes::all::OP_NUMEQUAL => 2,
            opcodes::all::OP_NUMEQUALVERIFY => 2,
            opcodes::all::OP_NUMNOTEQUAL => 2,
            opcodes::all::OP_LESSTHAN => 2,
            opcodes::all::OP_GREATERTHAN => 2,
            opcodes::all::OP_LESSTHANOREQUAL => 2,
            opcodes::all::OP_GREATERTHANOREQUAL => 2,
            opcodes::all::OP_MIN => 2,
            opcodes::all::OP_MAX => 2,
            opcodes::all::OP_WITHIN => 3,

            // Crypto
            opcodes::all::OP_RIPEMD160 => 1,
            opcodes::all::OP_SHA1 => 1,
            opcodes::all::OP_SHA256 => 1,
            opcodes::all::OP_HASH160 => 1,
            opcodes::all::OP_HASH256 => 1,
            opcodes::all::OP_CHECKSIG => 2,
            opcodes::all::OP_CHECKSIGVERIFY => 2,
            opcodes::all::OP_CHECKSIGADD => 3,

            // Locktime
            opcodes::all::OP_CLTV => 1,
            opcodes::all::OP_CSV => 1,

            _ => unreachable!(),
        }
    }

    /// Returns `true` if the operation returns nothing as output.
    pub const fn is_unit(self) -> bool {
        match self.0 {
            // Flow control
            opcodes::all::OP_VERIFY => true,

            // Bitwise logic
            opcodes::all::OP_EQUAL => false,
            opcodes::all::OP_EQUALVERIFY => true,

            // Arithmetic
            opcodes::all::OP_1ADD => false,
            opcodes::all::OP_1SUB => false,
            opcodes::all::OP_NEGATE => false,
            opcodes::all::OP_ABS => false,
            opcodes::all::OP_NOT => false,
            opcodes::all::OP_0NOTEQUAL => false,
            opcodes::all::OP_ADD => false,
            opcodes::all::OP_SUB => false,
            opcodes::all::OP_BOOLAND => false,
            opcodes::all::OP_BOOLOR => false,
            opcodes::all::OP_NUMEQUAL => false,
            opcodes::all::OP_NUMEQUALVERIFY => true,
            opcodes::all::OP_NUMNOTEQUAL => false,
            opcodes::all::OP_LESSTHAN => false,
            opcodes::all::OP_GREATERTHAN => false,
            opcodes::all::OP_LESSTHANOREQUAL => false,
            opcodes::all::OP_GREATERTHANOREQUAL => false,
            opcodes::all::OP_MIN => false,
            opcodes::all::OP_MAX => false,
            opcodes::all::OP_WITHIN => false,

            // Crypto
            opcodes::all::OP_RIPEMD160 => false,
            opcodes::all::OP_SHA1 => false,
            opcodes::all::OP_SHA256 => false,
            opcodes::all::OP_HASH160 => false,
            opcodes::all::OP_HASH256 => false,
            opcodes::all::OP_CHECKSIG => false,
            opcodes::all::OP_CHECKSIGVERIFY => true,
            opcodes::all::OP_CHECKSIGADD => false,

            // Locktime
            opcodes::all::OP_CLTV => true,
            opcodes::all::OP_CSV => true,

            _ => unreachable!(),
        }
    }

    /// Returns the corresponding [`bitcoin::Opcode`].
    pub const fn serialize(self) -> bitcoin::Opcode {
        self.0
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.0 {
            // Flow control
            opcodes::all::OP_VERIFY => f.write_str("verify"),

            // Bitwise logic
            opcodes::all::OP_EQUAL => f.write_str("equal"),
            opcodes::all::OP_EQUALVERIFY => f.write_str("equal_verify"),

            // Arithmetic
            opcodes::all::OP_1ADD => f.write_str("one_add"),
            opcodes::all::OP_1SUB => f.write_str("one_sub"),
            opcodes::all::OP_NEGATE => f.write_str("negate"),
            opcodes::all::OP_ABS => f.write_str("abs"),
            opcodes::all::OP_NOT => f.write_str("not"),
            opcodes::all::OP_0NOTEQUAL => f.write_str("zero_not_equal"),
            opcodes::all::OP_ADD => f.write_str("add"),
            opcodes::all::OP_SUB => f.write_str("sub"),
            opcodes::all::OP_BOOLAND => f.write_str("bool_and"),
            opcodes::all::OP_BOOLOR => f.write_str("bool_or"),
            opcodes::all::OP_NUMEQUAL => f.write_str("num_equal"),
            opcodes::all::OP_NUMEQUALVERIFY => f.write_str("num_equal_verify"),
            opcodes::all::OP_NUMNOTEQUAL => f.write_str("num_not_equal"),
            opcodes::all::OP_LESSTHAN => f.write_str("less_than"),
            opcodes::all::OP_GREATERTHAN => f.write_str("greater_than"),
            opcodes::all::OP_LESSTHANOREQUAL => f.write_str("less_than_or_equal"),
            opcodes::all::OP_GREATERTHANOREQUAL => f.write_str("greater_than_or_equal"),
            opcodes::all::OP_MIN => f.write_str("min"),
            opcodes::all::OP_MAX => f.write_str("max"),
            opcodes::all::OP_WITHIN => f.write_str("within"),

            // Crypto
            opcodes::all::OP_RIPEMD160 => f.write_str("ripemd160"),
            opcodes::all::OP_SHA1 => f.write_str("sha1"),
            opcodes::all::OP_SHA256 => f.write_str("sha256"),
            opcodes::all::OP_HASH160 => f.write_str("hash160"),
            opcodes::all::OP_HASH256 => f.write_str("hash256"),
            opcodes::all::OP_CHECKSIG => f.write_str("checksig"),
            opcodes::all::OP_CHECKSIGVERIFY => f.write_str("checksig_verify"),
            // Multisig operations are disabled in Tapscript
            // opcodes::all::OP_CHECKMULTISIG => f.write_str("checkmultisig"),
            // opcodes::all::OP_CHECKMULTISIGVERIFY => f.write_str("checkmultisigverify"),
            opcodes::all::OP_CHECKSIGADD => f.write_str("checksig_add"),

            // Locktime
            opcodes::all::OP_CLTV => f.write_str("check_locktime_verify"),
            opcodes::all::OP_CSV => f.write_str("check_sequence_verify"),

            _ => unreachable!(),
        }
    }
}
