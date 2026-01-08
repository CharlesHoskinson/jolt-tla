#!/bin/bash
# =============================================================================
# check_alignment.sh - Verify TLA+ and Lean constants stay aligned
# =============================================================================
# This script extracts key constants from both TLA+ and Lean implementations
# and verifies they match. Run this in CI to prevent drift.
#
# Usage: ./scripts/check_alignment.sh
# Exit: 0 if aligned, 1 if mismatched
# =============================================================================

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(dirname "$SCRIPT_DIR")"

echo "=== TLA+ / Lean Alignment Check ==="
echo "Repository: $REPO_ROOT"
echo ""

ERRORS=0

# -----------------------------------------------------------------------------
# Check 1: Registry Required Keys
# -----------------------------------------------------------------------------
echo "Checking registry required keys..."

TLA_REGISTRY="$REPO_ROOT/tla/Registry.tla"
LEAN_CONFIG_TAGS="$REPO_ROOT/lean/Jolt/Registry/ConfigTags.lean"

if [[ -f "$TLA_REGISTRY" ]] && [[ -f "$LEAN_CONFIG_TAGS" ]]; then
    TLA_KEYS=$(grep -oE 'JOLT_[A-Z0-9_]+_V[0-9]+' "$TLA_REGISTRY" 2>/dev/null | sort -u || true)
    LEAN_KEYS=$(grep -oE 'JOLT_[A-Z0-9_]+_V[0-9]+' "$LEAN_CONFIG_TAGS" 2>/dev/null | sort -u || true)

    if [[ "$TLA_KEYS" != "$LEAN_KEYS" ]]; then
        echo "MISMATCH: Registry keys differ between TLA and Lean"
        echo ""
        echo "TLA keys:"
        echo "$TLA_KEYS" | sed 's/^/  /'
        echo ""
        echo "Lean keys:"
        echo "$LEAN_KEYS" | sed 's/^/  /'
        echo ""
        ERRORS=$((ERRORS + 1))
    else
        echo "  OK: Registry keys match"
    fi
else
    echo "  SKIP: Registry files not found (TLA: $TLA_REGISTRY, Lean: $LEAN_CONFIG_TAGS)"
fi

# -----------------------------------------------------------------------------
# Check 2: Transcript Type Tags
# -----------------------------------------------------------------------------
echo "Checking transcript type tags..."

TLA_TRANSCRIPT="$REPO_ROOT/tla/Transcript.tla"
LEAN_TRANSCRIPT_TYPES="$REPO_ROOT/lean/Jolt/Transcript/Types.lean"

if [[ -f "$TLA_TRANSCRIPT" ]] && [[ -f "$LEAN_TRANSCRIPT_TYPES" ]]; then
    # Check TYPE_BYTES, TYPE_U64, TYPE_TAG, TYPE_VEC values
    TLA_TYPE_BYTES=$(grep -oE 'TYPE_BYTES[_A-Z]* *== *[0-9]+' "$TLA_TRANSCRIPT" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    TLA_TYPE_U64=$(grep -oE 'TYPE_U64[_A-Z]* *== *[0-9]+' "$TLA_TRANSCRIPT" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    TLA_TYPE_TAG=$(grep -oE 'TYPE_TAG[_A-Z]* *== *[0-9]+' "$TLA_TRANSCRIPT" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    TLA_TYPE_VEC=$(grep -oE 'TYPE_VEC[_A-Z]* *== *[0-9]+' "$TLA_TRANSCRIPT" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")

    LEAN_TYPE_BYTES=$(grep -oE 'TYPE_BYTES *:?=? *[0-9]+' "$LEAN_TRANSCRIPT_TYPES" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    LEAN_TYPE_U64=$(grep -oE 'TYPE_U64 *:?=? *[0-9]+' "$LEAN_TRANSCRIPT_TYPES" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    LEAN_TYPE_TAG=$(grep -oE 'TYPE_TAG *:?=? *[0-9]+' "$LEAN_TRANSCRIPT_TYPES" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")
    LEAN_TYPE_VEC=$(grep -oE 'TYPE_VEC *:?=? *[0-9]+' "$LEAN_TRANSCRIPT_TYPES" 2>/dev/null | grep -oE '[0-9]+$' || echo "not found")

    TYPE_MISMATCH=0
    [[ "$TLA_TYPE_BYTES" != "$LEAN_TYPE_BYTES" ]] && TYPE_MISMATCH=1
    [[ "$TLA_TYPE_U64" != "$LEAN_TYPE_U64" ]] && TYPE_MISMATCH=1
    [[ "$TLA_TYPE_TAG" != "$LEAN_TYPE_TAG" ]] && TYPE_MISMATCH=1
    [[ "$TLA_TYPE_VEC" != "$LEAN_TYPE_VEC" ]] && TYPE_MISMATCH=1

    if [[ $TYPE_MISMATCH -eq 1 ]]; then
        echo "MISMATCH: Transcript type tags differ"
        echo "  TLA:  BYTES=$TLA_TYPE_BYTES U64=$TLA_TYPE_U64 TAG=$TLA_TYPE_TAG VEC=$TLA_TYPE_VEC"
        echo "  Lean: BYTES=$LEAN_TYPE_BYTES U64=$LEAN_TYPE_U64 TAG=$LEAN_TYPE_TAG VEC=$LEAN_TYPE_VEC"
        ERRORS=$((ERRORS + 1))
    else
        echo "  OK: Transcript type tags match (or not yet defined in TLA)"
    fi
else
    echo "  SKIP: Transcript files not found"
fi

# -----------------------------------------------------------------------------
# Check 3: Domain Tags
# -----------------------------------------------------------------------------
echo "Checking domain tags..."

TLA_HASH="$REPO_ROOT/tla/Hash.tla"
LEAN_TAG_VALIDATION="$REPO_ROOT/lean/Jolt/Transcript/TagValidation.lean"

if [[ -f "$TLA_HASH" ]]; then
    TLA_TAGS=$(grep -oE '"JOLT/[A-Z0-9/_]+/V[0-9]+"' "$TLA_HASH" 2>/dev/null | sort -u | wc -l || echo "0")
    echo "  Found $TLA_TAGS domain tags in TLA Hash.tla"
else
    echo "  SKIP: Hash.tla not found"
fi

# -----------------------------------------------------------------------------
# Summary
# -----------------------------------------------------------------------------
echo ""
echo "=== Summary ==="
if [[ $ERRORS -eq 0 ]]; then
    echo "All alignment checks passed!"
    exit 0
else
    echo "Found $ERRORS alignment issues. Please fix before merging."
    exit 1
fi
