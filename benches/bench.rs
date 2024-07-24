mod contains;
mod insert;

use criterion::{criterion_group, criterion_main};

criterion_main!(benches);
criterion_group!(benches, insert::bench, contains::bench);

/// Linear-feedback shift register based PRNG.
///
/// Generates 65,535 unique values before cycling.
#[derive(Debug, Clone)]
pub struct Lfsr(u16);

impl Default for Lfsr {
    fn default() -> Self {
        Self(42)
    }
}

impl Lfsr {
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> u16 {
        let lsb = self.0 & 1;
        self.0 >>= 1;
        if lsb == 1 {
            self.0 ^= 0xD008;
        }
        assert_ne!(self.0, 42, "LFSR rollover");
        self.0
    }
}
