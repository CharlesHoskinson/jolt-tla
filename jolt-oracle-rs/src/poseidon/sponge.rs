//! Poseidon sponge construction.
//!
//! Implements the sponge-based hash using the Poseidon permutation.

use super::{permute, RATE, WIDTH};
use crate::field::Fr;

/// Sponge operation mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Absorbing input elements
    Absorbing,
    /// Squeezing output elements
    Squeezing,
}

/// Sponge state for incremental hashing.
#[derive(Debug, Clone)]
pub struct SpongeState {
    /// Internal state (width elements)
    state: [Fr; WIDTH],
    /// Current position in rate portion
    pos: usize,
    /// Current mode
    mode: Mode,
}

impl SpongeState {
    /// Create a new sponge state initialized to zeros.
    pub fn new() -> Self {
        Self {
            state: [Fr::ZERO; WIDTH],
            pos: 0,
            mode: Mode::Absorbing,
        }
    }

    /// Absorb a single field element per spec §8.4 absorb_fr.
    ///
    /// 1. if mode == SQUEEZE: permute(); mode = ABSORB; pos = 0
    /// 2. state[pos] += x; pos += 1
    /// 3. if pos == r: permute(); pos = 0
    pub fn absorb_one(&mut self, x: Fr) {
        // Step 1: If squeezing, switch to absorb mode
        if self.mode == Mode::Squeezing {
            self.state = permute(&self.state);
            self.mode = Mode::Absorbing;
            self.pos = 0;
        }

        // Step 2: state[pos] += x
        self.state[self.pos] = self.state[self.pos] + x;
        self.pos += 1;

        // Step 3: if pos == r: permute(); pos = 0
        if self.pos >= RATE {
            self.state = permute(&self.state);
            self.pos = 0;
        }
    }

    /// Absorb multiple field elements.
    pub fn absorb(&mut self, elements: &[Fr]) {
        for &x in elements {
            self.absorb_one(x);
        }
    }

    /// Finalize absorption and switch to squeezing per spec §8.4.
    ///
    /// Per spec: if mode == ABSORB: permute(); mode = SQUEEZE; pos = 0
    fn finalize(&mut self) {
        if self.mode == Mode::Absorbing {
            self.state = permute(&self.state);
            self.mode = Mode::Squeezing;
            self.pos = 0;
        }
    }

    /// Squeeze a single field element per spec §8.4 squeeze_fr.
    ///
    /// 1. if mode == ABSORB: permute(); mode = SQUEEZE; pos = 0
    /// 2. y = state[pos]; pos += 1
    /// 3. if pos == r: permute(); pos = 0
    /// 4. return y
    pub fn squeeze_one(&mut self) -> Fr {
        // Step 1: If absorbing, switch to squeeze mode
        self.finalize();

        // Step 2: y = state[pos]
        let result = self.state[self.pos];
        self.pos += 1;

        // Step 3: if pos == r: permute(); pos = 0
        if self.pos >= RATE {
            self.state = permute(&self.state);
            self.pos = 0;
        }

        result
    }

    /// Squeeze n field elements.
    pub fn squeeze(&mut self, n: usize) -> Vec<Fr> {
        let mut result = Vec::with_capacity(n);
        for _ in 0..n {
            result.push(self.squeeze_one());
        }
        result
    }
}

impl Default for SpongeState {
    fn default() -> Self {
        Self::new()
    }
}

/// Hash an array of field elements to a single field element.
pub fn hash(elements: &[Fr]) -> Fr {
    let mut sponge = SpongeState::new();
    sponge.absorb(elements);
    sponge.squeeze_one()
}

/// Hash an array of field elements to n field elements.
pub fn hash_n(elements: &[Fr], n: usize) -> Vec<Fr> {
    let mut sponge = SpongeState::new();
    sponge.absorb(elements);
    sponge.squeeze(n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_empty() {
        let result = hash(&[]);
        // Should produce a deterministic non-zero output
        assert_ne!(result, Fr::ZERO);
    }

    #[test]
    fn test_hash_deterministic() {
        let elements = [Fr::ONE, Fr::from_u64(2), Fr::from_u64(3)];
        let result1 = hash(&elements);
        let result2 = hash(&elements);
        assert_eq!(result1, result2);
    }

    #[test]
    fn test_hash_different_inputs() {
        let result1 = hash(&[Fr::ONE]);
        let result2 = hash(&[Fr::from_u64(2)]);
        assert_ne!(result1, result2);
    }
}
