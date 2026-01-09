import Tests.Basic
import Tests.Checker
import Tests.Transcript
import Tests.Integration
import Tests.TLAAttacks

/-!
# Tests

Root module for the NearFall test suite.

## Test Modules
* `Tests.Basic` - Basic sanity tests (types, constructors)
* `Tests.Checker` - Checker module tests (step function, trace validation)
* `Tests.Transcript` - Transcript module tests (absorb, domain separation)
* `Tests.Integration` - End-to-end integration tests
* `Tests.TLAAttacks` - TLA+ attack prevention tests (v0.2.0)

## Test Summary

### Tests.Basic (22 tests)
- Version string validation
- Type construction (Digest, FieldElem, ChallengeType)
- Label distinctness
- Event distinctness
- TranscriptState/ExpectedInputs/CheckState initial values

### Tests.Checker (25+ tests)
- Step function behavior for all 9 event types
- Trace validation acceptance/rejection
- Complex trace sequences
- State transition verification

### Tests.Transcript (20+ tests)
- Absorb function correctness
- After squeeze behavior
- Domain separation properties
- Absorption order sensitivity

### Tests.Integration (20+ tests)
- Valid trace examples (5 scenarios)
- Invalid trace rejection (6 scenarios)
- Security property verification
- Soundness theorem application
- Trace composition
- State monotonicity
- Decidability verification

### Tests.TLAAttacks (40+ tests) - v0.2.0
- Attack 1: Skip Chunk detection
- Attack 2: Splice Execution prevention
- Attack 3: Cross-Config prevention
- Attack 4: Memory Forgery detection
- Attack 5: IO Forgery detection
- Attack 6: Replay prevention
- Attack 7: Prefix Proof rejection
- Attack 8: Root Forgery detection
- CheckerV2 integration tests
- VM State safety tests
- Invariant count verification

## References
* Jolt Spec §1-§15 for test requirements
* jolt-tla/tla/Invariants.tla for TLA+ attack tests
-/
