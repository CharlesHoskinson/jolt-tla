-- Import all modules for the library
import NearFall.Basic

/-!
# NearFall Lean 4 Kernel

Root module for the NearFall formal verification kernel.

This kernel proves trace-based conformance for zkVM host + Halo2 wrapper.

## Security Guarantee
`check_trace OK → obligations_satisfied`

## Main Modules
* `NearFall.Types` - Core type definitions (Event, CheckState, etc.)
* `NearFall.Encoding` - CBOR deterministic encoding
* `NearFall.Transcript` - Poseidon transcript state machine
* `NearFall.Checker` - Trace validation state machine
* `NearFall.Soundness` - Main soundness theorem

## References
* Jolt Specification §1-§15
* TLA+ Invariants: INV_SAFE_*, INV_BIND_*, INV_ATK_*
-/
