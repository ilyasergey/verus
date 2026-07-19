#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] u64_native_little_endian_round_trip verus_code! {
        use vstd::prelude::*;

        fn round_trip(x: u64) -> (out: u64)
            ensures out == x,
        {
            proof { vstd::bytes::lemma_auto_spec_u64_to_from_le_bytes(); }
            let bytes = x.to_le_bytes();
            u64::from_le_bytes(bytes)
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] u64_native_little_endian_wrong_byte_order verus_code! {
        use vstd::prelude::*;

        fn wrong() -> (bytes: [u8; 8])
            ensures bytes[0] == 1, // FAILS
        {
            0u64.to_le_bytes()
        }
    } => Err(err) => assert_one_fails(err)
}
