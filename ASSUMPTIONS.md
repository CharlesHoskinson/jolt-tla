# Assumption Registry (TCB Ledger)

This document catalogs all assumptions used in the Jolt specification proofs.
It serves as a Trusted Computing Base (TCB) ledger for auditing.

## Cryptographic Assumptions

| ID | Statement | Used In | Justification |
|----|-----------|---------|---------------|
| CRYPTO-01 | `HInjectiveOnCritical`: Hash function H is injective on the typed Preimage domain (TB, SE, TR constructors) | CryptoModel.tla, AttackLemmas.tla | Collision resistance of Poseidon (128-bit security) |
| CRYPTO-02 | Domain separation: Different tags produce different hash outputs (derived from CRYPTO-01 + tagged constructors) | CryptoModel.tla | Follows from CRYPTO-01 via TBInjective lemma |

## VM Assumptions

| ID | Statement | Used In | Justification |
|----|-----------|---------|---------------|
| VM-01 | `STEP_FN` preserves x0 = 0 (register zero invariant) | SafetyInduction.tla | RISC-V ISA specification: x0 is hardwired to 0 |
| VM-02 | `STEP_FN` monotonically increases step_counter | SafetyInduction.tla | Step counter is incremented on each instruction |
| VM-03 | Halt is irreversible: once halted = 1, it remains 1 | SafetyInduction.tla | Execution cannot resume after HALT instruction |

## Fairness Assumptions

| ID | Statement | Used In | Justification |
|----|-----------|---------|---------------|
| FAIR-01 | Weak fairness on `StartExecution` in INIT phase | LivenessProofs.tla, Liveness.lean | Scheduler eventually allows transition |
| FAIR-02 | Weak fairness on `ExecuteChunk` in EXECUTING phase | LivenessProofs.tla, Liveness.lean | Scheduler eventually allows chunk execution |

## Modeling Facts (PROVED, not assumed)

These are lemmas derived from the model definitions, not axioms.

| ID | Statement | Proved In | Status |
|----|-----------|-----------|--------|
| MODEL-01 | Trace allows stuttering at any step (matches `[Next]_vars`) | Trace.lean (StepOrStutter def), JoltSpec.tla | Definitional |
| MODEL-02 | `Next` decomposes into `ProgressStep` or `NonProgressStep` | SafetyInduction.tla (NextDecomposes), Variant.lean (next_decomposes) | LEMMA |
| MODEL-03 | `ProgressStep` strictly decreases variant | SafetyInduction.tla (VariantDecrease), Variant.lean (variant_decreases) | LEMMA |
| MODEL-04 | Non-progress actions don't increase variant | SafetyInduction.tla (VariantNonIncrease), Variant.lean (variant_nonIncrease) | LEMMA |

## Conditional Assumptions (for unconditional liveness)

| ID | Statement | Used In | Notes |
|----|-----------|---------|-------|
| COND-01 | Program halts OR execution is bounded by MAX_CHUNKS | LivenessProofs.tla | Required for unconditional termination; wrapper enforces MAX_CHUNKS bound |

## Encoding Assumptions

| ID | Statement | Used In | Justification |
|----|-----------|---------|---------------|
| ENC-01 | `EncodeState` is injective: distinct states produce distinct encodings | AttackLemmas.tla | Structural property of encoding function |
| ENC-02 | All state encodings are in `CriticalPreimage` (SE constructor) | TypeOK.tla | Follows from EncodeStateMembership lemma |

## Assumption Dependency Graph

```
CRYPTO-01 (HInjectiveOnCritical)
    |
    +-- CRYPTO-02 (DomainSeparation) via TBInjective
    |
    +-- AttackLemmas: DigestBinding via ENC-01

VM-01, VM-02, VM-03
    |
    +-- SafetyInduction: IndInvInductive

FAIR-01, FAIR-02
    |
    +-- LivenessProofs: ProgressFromInit, WrapperTerminates
    +-- Liveness.lean: progress_from_init, eventually_terminal

MODEL-02, MODEL-03, MODEL-04
    |
    +-- Termination via variant decrease
```

## Verification Status

| Track | Assumptions Used | Verification Tool | Status |
|-------|------------------|-------------------|--------|
| TLA+ Safety | CRYPTO-01, VM-01-03, ENC-01-02 | TLAPS | Pending |
| TLA+ Liveness | FAIR-01-02, COND-01 | TLAPS (WF/ENABLED) | Pending |
| Lean Safety | VM-01-03 | Lean 4 | Pending |
| Lean Liveness | FAIR-01-02, MODEL-02-04 | Lean 4 (Red Team) | Pending |

## Proof Obligation Map

Complete mapping of theorems to assumptions and verification status.

### TLA+ Proof Modules

| File | Theorems | Assumptions | Temporal? | Status |
|------|----------|-------------|-----------|--------|
| `CryptoModel.tla` | TBInjective, SEInjective, ConstructorDisjoint, DomainSeparation | CRYPTO-01 | Safety | Pending |
| `TypeOK.tla` | TypeOKInductive, VariantNonNeg, EncodeStateMembership | - | Safety | Pending |
| `SafetyInduction.tla` | IndInvInductive, NextDecomposes, VariantNonIncrease, VariantDecrease | VM-01,02,03 | Safety | Pending |
| `AttackLemmas.tla` | EncodeStateInjective, DigestBinding, NoSpliceAttackSound, NoCrossProgramSplice | CRYPTO-01, ENC-01 | Safety | Pending |
| `LivenessProofs.tla` | ProgressFromInit, ProgressFromExecuting, WrapperTerminates, InitLeadsToTerminal | FAIR-01,02 | Temporal | Pending |

### Lean Proof Modules

| File | Theorems | Assumptions | Status |
|------|----------|-------------|--------|
| `Trace.lean` | stutter_valid, step_implies_stepOrStutter, terminal_absorbing, terminal_forever | - | Complete |
| `Temporal.lean` | infOften_iff_infOften', always_eventually_duality, eventually_always_duality, leadsTo_trans | - | Complete |
| `Fairness.lean` | weakFair_iff_weakFair', strongFair_implies_weakFair, weakFair_usable, strongFair_usable | - | Complete |
| `Variant.lean` | variant_nonneg, variant_bounded, step_classification, next_decomposes, variant_decreases, variant_nonIncrease | - | Red Team |
| `Liveness.lean` | progress_from_init, eventually_not_init, progress_from_executing, eventually_terminal, complete_liveness | FAIR-01,02 | Red Team |
| `Progress.lean` | no_deadlock, init_can_progress, executing_can_progress, terminal_only_stutter | - | Complete |
| `Alignment.lean` | startExecution_def, executeChunk_def, stepOrStutter_def, variant_def, enabled_def, weakFair_def | - | Build Artifact |

### Red Team Targets

Theorems requiring automated proof generation:

| Module | Theorem | Priority | Notes |
|--------|---------|----------|-------|
| `Variant.lean` | variant_decreases_executeChunk | High | Core termination |
| `Variant.lean` | variant_nonterminal_pos | High | Variant > 0 in non-terminal |
| `Liveness.lean` | progress_from_init | High | INIT ~> not INIT |
| `Liveness.lean` | eventually_terminal | Critical | Main termination theorem |
| `Liveness.lean` | complete_liveness | High | Full liveness chain |
| `Alignment.lean` | chunks_consecutive | Medium | Inductive invariant |

### Cross-Track Alignment

| Lean Definition | TLA+ Definition | Alignment Lemma |
|-----------------|-----------------|-----------------|
| `CommittedChunks` | `CommittedChunks(sys)` | `committedChunks_def` |
| `StepOrStutter` | `[Next]_vars` | `stepOrStutter_def` |
| `ProgressStep` | `ProgressStep` | `progressStep_def` |
| `WeakFair` | `WF_vars(A)` | `weakFair_def` |
| `variant` | `Variant(s)` | `variant_def` |

## Audit Notes

- All assumptions MUST be reviewed before deployment
- Cryptographic assumptions depend on 128-bit security of Poseidon
- VM assumptions must be validated against RISC-V reference implementation
- Fairness assumptions are standard scheduler properties
- Red Team targets should be processed before final release
- Alignment.lean must compile without sorry for semantic integrity
