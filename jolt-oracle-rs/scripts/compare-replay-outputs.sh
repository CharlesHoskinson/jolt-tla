#!/bin/bash
# Compare replay test outputs from different platforms.
#
# This script compares JSON output files from run-replay-tests.sh
# to verify all platforms produce identical results.
#
# Usage:
#   ./scripts/compare-replay-outputs.sh <file1> <file2> [file3...]
#
# Exit codes:
#   0 - All outputs match
#   1 - Outputs differ
#   2 - Script error

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <file1> <file2> [file3...]"
    echo ""
    echo "Compare replay test outputs from different platforms."
    exit 2
fi

echo -e "${BLUE}=== Cross-Platform Replay Comparison ===${NC}"
echo ""

# Verify all files exist
for file in "$@"; do
    if [[ ! -f "$file" ]]; then
        echo -e "${RED}Error: File not found: $file${NC}"
        exit 2
    fi
done

# Extract results from each file and compare
REFERENCE_FILE="$1"
REFERENCE_PLATFORM=$(jq -r '.platform' "$REFERENCE_FILE")
echo "Reference: $REFERENCE_FILE ($REFERENCE_PLATFORM)"

FAILURES=0
TOTAL_TESTS=0

# Get all test names from reference
TEST_NAMES=$(jq -r '.results | keys[]' "$REFERENCE_FILE")

for file in "${@:2}"; do
    PLATFORM=$(jq -r '.platform' "$file")
    echo ""
    echo -e "${BLUE}Comparing with: $file ($PLATFORM)${NC}"

    for test in $TEST_NAMES; do
        TOTAL_TESTS=$((TOTAL_TESTS + 1))

        # Extract results
        REF_RESULT=$(jq -r ".results[\"$test\"]" "$REFERENCE_FILE")
        CMP_RESULT=$(jq -r ".results[\"$test\"]" "$file")

        if [[ "$REF_RESULT" == "$CMP_RESULT" ]]; then
            echo -e "  ${GREEN}PASS${NC}: $test"
        else
            echo -e "  ${RED}FAIL${NC}: $test"
            echo "    Reference ($REFERENCE_PLATFORM):"
            echo "      $REF_RESULT" | head -c 200
            echo ""
            echo "    Compared ($PLATFORM):"
            echo "      $CMP_RESULT" | head -c 200
            echo ""
            FAILURES=$((FAILURES + 1))
        fi
    done
done

echo ""
echo "=== Summary ==="
PASSED=$((TOTAL_TESTS - FAILURES))
echo "Total comparisons: $TOTAL_TESTS"
echo -e "Passed: ${GREEN}$PASSED${NC}"
echo -e "Failed: ${RED}$FAILURES${NC}"

if [[ $FAILURES -eq 0 ]]; then
    echo ""
    echo -e "${GREEN}=== All platforms produce identical output ===${NC}"
    exit 0
else
    echo ""
    echo -e "${RED}=== FAILURE: Platform outputs differ ===${NC}"
    exit 1
fi
