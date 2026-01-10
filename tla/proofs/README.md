# TLA+ Proof Modules

This directory contains TLAPS proof modules for unbounded/infinite-state verification of the Jolt specification.

## Toolchain Requirements

### TLAPS Installation

Requires TLAPS with temporal reasoning and ENABLED expansion support.

```bash
# Verify TLAPS is installed and backends are configured
tlapm --config

# Expected output should show Isabelle and Zenon backends
```

### Version Requirements

- **TLAPS**: >= 1.5.0 (with temporal reasoning support)
- **Isabelle**: >= 2021 (backend prover)
- **Zenon**: >= 0.8.5 (SMT integration)

## Proof Modules

| Module | Purpose | Type |
|--------|---------|------|
| `CryptoModel.tla` | Tagged constructors + scoped hash injectivity | Safety |
| `TypeOK.tla` | Type invariant + encoding membership | Safety |
| `SafetyInduction.tla` | Inductive invariant + variant lemmas | Safety |
| `AttackLemmas.tla` | Encoding injectivity + digest binding | Safety |
| `LivenessProofs.tla` | WF/ENABLED leads-to theorems | Temporal |

## Verification Commands

### Step 1: Verify Toolchain

```bash
# Check TLAPS configuration
tlapm --config

# Ensure backends are found:
# - Isabelle backend: OK
# - Zenon backend: OK
```

### Step 2: Run TLC First (Smoke Test)

Always run TLC on small models before TLAPS to catch false lemmas:

```bash
# From jolt-tla root
java -jar tla2tools.jar -config Jolt.cfg JoltSpec.tla
```

### Step 3: TLAPS Proofs

```bash
# Type invariant
tlapm --threads 4 tla/proofs/TypeOK.tla

# Crypto model
tlapm --threads 4 tla/proofs/CryptoModel.tla

# Safety induction (after TypeOK succeeds)
tlapm --threads 4 tla/proofs/SafetyInduction.tla

# Attack lemmas
tlapm --threads 4 tla/proofs/AttackLemmas.tla

# Liveness (requires ENABLED support)
tlapm --threads 4 tla/proofs/LivenessProofs.tla
```

## Proof Discipline

### Keep Obligations Small

- Use `LOCAL` definitions to hide intermediate terms
- Use `HIDE` to reduce proof obligation size
- Break complex proofs into small `<n>k.` steps

### Proof Structure Pattern

```tla
THEOREM Example ==
    P => Q
<1>1. ASSUME P
<1>2. \* Intermediate step
      BY <1>1 DEF SomeDef
<1>3. Q
      BY <1>2
<1>4. QED BY <1>1, <1>3
```

### Temporal Proofs (WF/ENABLED)

For `P ~> Q` under weak fairness, prove four obligations:

1. `P => ENABLED <<A>>_vars` (action is enabled)
2. `P /\ <<A>>_vars => Q'` (action achieves goal)
3. `P /\ [Next]_vars => P' \/ Q'` (stuttering-compatible)
4. `P /\ [Next]_vars => (P' => (ENABLED <<A>>_vars)')` (enabledness stability)

## Assumptions

All cryptographic and VM assumptions are documented in:
- `../ASSUMPTIONS.md` (TCB ledger)
- Each module's header comments

Key assumptions:
- `CRYPTO-01`: `HInjectiveOnCritical` (hash injectivity on typed domain)
- `VM-01`: Register x0 preservation
- `FAIR-01`, `FAIR-02`: Weak fairness on transitions

## CI Integration

The CI pipeline runs:

1. TLC model checking (smoke test)
2. TLAPS proof verification
3. Lean proof verification (parallel track)

See `.github/workflows/tlaplus.yml` for CI configuration.

## Contingency Plan

If TLAPS temporal proofs become unstable:

1. Keep safety proofs (variant lemmas) in TLAPS
2. Use Lean as primary liveness oracle
3. Document any skipped temporal theorems

See `../ASSUMPTIONS.md` for fallback procedures.
