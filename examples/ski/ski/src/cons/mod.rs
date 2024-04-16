pub mod air;
pub mod columns;

const CONST_PTR_TAG: u16 = 42;

const CAR_TAG: u16 = 101;
const CDR_TAG: u16 = 102;

/// A chip that implements the CPU.
#[derive(Default)]
pub struct ConsChip;
