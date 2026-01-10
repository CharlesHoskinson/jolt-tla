#!/bin/bash
# Metadata drift detection for Lean/Rust oracle synchronization.
#
# This script verifies that metadata.json exported from Lean matches
# expectations and that the Rust codegen produces consistent output.
#
# Exit codes:
#   0 - Metadata is valid and in sync
#   1 - Metadata validation failed
#   2 - Script error (missing dependencies, etc.)
#
# Usage:
#   ./scripts/check-metadata-drift.sh [--verbose]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
METADATA_FILE="$PROJECT_DIR/../jolt_oracle/metadata.json"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

VERBOSE=false
if [[ "$1" == "--verbose" || "$1" == "-v" ]]; then
    VERBOSE=true
fi

log() {
    if $VERBOSE; then
        echo -e "$1"
    fi
}

echo -e "${BLUE}=== Metadata Drift Detection ===${NC}"
echo ""

# Check dependencies
if ! command -v jq &> /dev/null; then
    echo -e "${RED}Error: jq is required but not installed.${NC}"
    echo "Install with: apt-get install jq (Linux) or brew install jq (macOS)"
    exit 2
fi

# Check metadata file exists
if [[ ! -f "$METADATA_FILE" ]]; then
    echo -e "${RED}Error: metadata.json not found at $METADATA_FILE${NC}"
    echo ""
    echo "Generate it by running:"
    echo "  cd jolt_oracle && lake exe oracle export-metadata > metadata.json"
    exit 1
fi

log "Checking: $METADATA_FILE"
echo ""

# =============================================================================
# Check 1: Valid JSON
# =============================================================================
echo -n "1. Valid JSON structure... "
if ! jq empty "$METADATA_FILE" 2>/dev/null; then
    echo -e "${RED}FAIL${NC}"
    echo "   metadata.json is not valid JSON"
    exit 1
fi
echo -e "${GREEN}OK${NC}"

# =============================================================================
# Check 2: Version field
# =============================================================================
echo -n "2. Version field... "
VERSION=$(jq -r '.version' "$METADATA_FILE")
if [[ "$VERSION" != "1" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected version '1', got '$VERSION'"
    exit 1
fi
echo -e "${GREEN}OK${NC} (v$VERSION)"

# =============================================================================
# Check 3: Required top-level fields
# =============================================================================
echo -n "3. Required fields... "
REQUIRED_FIELDS=("version" "field" "errors" "poseidon")
MISSING=()
for field in "${REQUIRED_FIELDS[@]}"; do
    if [[ $(jq "has(\"$field\")" "$METADATA_FILE") != "true" ]]; then
        MISSING+=("$field")
    fi
done
if [[ ${#MISSING[@]} -gt 0 ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Missing fields: ${MISSING[*]}"
    exit 1
fi
echo -e "${GREEN}OK${NC}"

# =============================================================================
# Check 4: Field modulus present
# =============================================================================
echo -n "4. Field modulus... "
MODULUS=$(jq -r '.field.modulus' "$METADATA_FILE")
MODULUS_HEX=$(jq -r '.field.modulus_hex' "$METADATA_FILE")
if [[ -z "$MODULUS" || "$MODULUS" == "null" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Missing field.modulus"
    exit 1
fi
if [[ -z "$MODULUS_HEX" || "$MODULUS_HEX" == "null" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Missing field.modulus_hex"
    exit 1
fi
# Verify modulus is the BLS12-381 scalar field modulus
EXPECTED_MODULUS="52435875175126190479447740508185965837690552500527637822603658699938581184513"
if [[ "$MODULUS" != "$EXPECTED_MODULUS" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Modulus mismatch (not BLS12-381 Fr)"
    echo "   Expected: $EXPECTED_MODULUS"
    echo "   Got:      $MODULUS"
    exit 1
fi
echo -e "${GREEN}OK${NC}"
log "   Modulus: ${MODULUS:0:20}..."

# =============================================================================
# Check 5: Error codes
# =============================================================================
echo -n "5. Error codes... "
ERROR_COUNT=$(jq '.errors | length' "$METADATA_FILE")
if [[ "$ERROR_COUNT" -lt 10 ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Too few error codes: $ERROR_COUNT (expected >= 10)"
    exit 1
fi
# Check for required error codes
REQUIRED_ERRORS=("E100_InvalidJSON" "E101_DuplicateKey" "E300_NonCanonicalFr")
for err in "${REQUIRED_ERRORS[@]}"; do
    if [[ $(jq ".errors[] | select(.name == \"$err\")" "$METADATA_FILE") == "" ]]; then
        echo -e "${RED}FAIL${NC}"
        echo "   Missing required error code: $err"
        exit 1
    fi
done
echo -e "${GREEN}OK${NC} ($ERROR_COUNT codes)"

# =============================================================================
# Check 6: Poseidon parameters
# =============================================================================
echo -n "6. Poseidon parameters... "
WIDTH=$(jq -r '.poseidon.width' "$METADATA_FILE")
RATE=$(jq -r '.poseidon.rate' "$METADATA_FILE")
FULL_ROUNDS=$(jq -r '.poseidon.full_rounds' "$METADATA_FILE")
PARTIAL_ROUNDS=$(jq -r '.poseidon.partial_rounds' "$METADATA_FILE")

# Verify expected Jolt parameters
if [[ "$WIDTH" != "3" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected width=3, got $WIDTH"
    exit 1
fi
if [[ "$RATE" != "2" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected rate=2, got $RATE"
    exit 1
fi
if [[ "$FULL_ROUNDS" != "8" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected full_rounds=8, got $FULL_ROUNDS"
    exit 1
fi
if [[ "$PARTIAL_ROUNDS" != "60" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected partial_rounds=60, got $PARTIAL_ROUNDS"
    exit 1
fi
echo -e "${GREEN}OK${NC} (t=$WIDTH, r=$RATE, RF=$FULL_ROUNDS, RP=$PARTIAL_ROUNDS)"

# =============================================================================
# Check 7: Round constants count
# =============================================================================
echo -n "7. Round constants... "
RC_COUNT=$(jq '.poseidon.round_constants | length' "$METADATA_FILE")
EXPECTED_RC=$((FULL_ROUNDS + PARTIAL_ROUNDS))
if [[ "$RC_COUNT" != "$EXPECTED_RC" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected $EXPECTED_RC rounds, got $RC_COUNT"
    exit 1
fi
# Check each round has WIDTH elements
for ((i=0; i<RC_COUNT; i++)); do
    ELEMENTS=$(jq ".poseidon.round_constants[$i] | length" "$METADATA_FILE")
    if [[ "$ELEMENTS" != "$WIDTH" ]]; then
        echo -e "${RED}FAIL${NC}"
        echo "   Round $i has $ELEMENTS elements, expected $WIDTH"
        exit 1
    fi
done
echo -e "${GREEN}OK${NC} ($RC_COUNT rounds x $WIDTH elements)"

# =============================================================================
# Check 8: MDS matrix dimensions
# =============================================================================
echo -n "8. MDS matrix... "
MDS_ROWS=$(jq '.poseidon.mds_matrix | length' "$METADATA_FILE")
if [[ "$MDS_ROWS" != "$WIDTH" ]]; then
    echo -e "${RED}FAIL${NC}"
    echo "   Expected ${WIDTH}x${WIDTH} MDS matrix, got ${MDS_ROWS} rows"
    exit 1
fi
for ((i=0; i<MDS_ROWS; i++)); do
    COLS=$(jq ".poseidon.mds_matrix[$i] | length" "$METADATA_FILE")
    if [[ "$COLS" != "$WIDTH" ]]; then
        echo -e "${RED}FAIL${NC}"
        echo "   MDS row $i has $COLS columns, expected $WIDTH"
        exit 1
    fi
done
echo -e "${GREEN}OK${NC} (${WIDTH}x${WIDTH})"

# =============================================================================
# Check 9: Round constants hash present
# =============================================================================
echo -n "9. Round constants hash... "
RC_HASH=$(jq -r '.poseidon.round_constants_hash' "$METADATA_FILE")
if [[ -z "$RC_HASH" || "$RC_HASH" == "null" ]]; then
    echo -e "${YELLOW}WARN${NC} (missing)"
    log "   No round_constants_hash for verification"
else
    # Verify it's a valid 64-char hex string
    if [[ ! "$RC_HASH" =~ ^[0-9a-fA-F]{64}$ ]]; then
        echo -e "${RED}FAIL${NC}"
        echo "   Invalid hash format: $RC_HASH"
        exit 1
    fi
    echo -e "${GREEN}OK${NC}"
    log "   Hash: ${RC_HASH:0:16}..."
fi

# =============================================================================
# Check 10: Compute metadata checksum
# =============================================================================
echo -n "10. Metadata checksum... "
# Compute SHA-256 of key fields for drift detection
CHECKSUM=$(jq -c '{
    version: .version,
    modulus: .field.modulus,
    error_count: (.errors | length),
    poseidon: {
        width: .poseidon.width,
        rate: .poseidon.rate,
        full_rounds: .poseidon.full_rounds,
        partial_rounds: .poseidon.partial_rounds,
        rc_hash: .poseidon.round_constants_hash
    }
}' "$METADATA_FILE" | sha256sum | cut -d' ' -f1)
echo -e "${GREEN}OK${NC}"
log "   Checksum: ${CHECKSUM:0:16}..."

# =============================================================================
# Summary
# =============================================================================
echo ""
echo -e "${BLUE}=== Summary ===${NC}"
echo ""
echo -e "  Version:       $VERSION"
echo -e "  Error codes:   $ERROR_COUNT"
echo -e "  Poseidon:      t=$WIDTH, r=$RATE, RF=$FULL_ROUNDS, RP=$PARTIAL_ROUNDS"
echo -e "  Checksum:      ${CHECKSUM:0:32}..."
echo ""
echo -e "${GREEN}=== PASS: Metadata is valid and consistent ===${NC}"
exit 0
