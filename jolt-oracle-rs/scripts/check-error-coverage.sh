#!/bin/bash
# Check that all ErrorCode variants are tested
#
# This script reads error codes from metadata.json and checks that each
# error code is referenced in at least one test file.
#
# Exit codes:
#   0 - All error codes are covered
#   1 - Some error codes are not covered
#   2 - Script error (missing dependencies, etc.)
#
# Usage:
#   ./scripts/check-error-coverage.sh [--verbose]

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

# Check dependencies
if ! command -v jq &> /dev/null; then
    echo -e "${RED}Error: jq is required but not installed.${NC}"
    echo "Install with: apt-get install jq (Linux) or brew install jq (macOS)"
    exit 2
fi

# Check metadata file exists
if [[ ! -f "$METADATA_FILE" ]]; then
    echo -e "${RED}Error: metadata.json not found at $METADATA_FILE${NC}"
    exit 2
fi

echo -e "${BLUE}=== ErrorCode Coverage Check ===${NC}"
echo ""

# Extract all error code names from metadata.json
ERROR_CODES=$(jq -r '.errors[].name' "$METADATA_FILE")
TOTAL_CODES=$(echo "$ERROR_CODES" | wc -l | tr -d ' ')

echo "Found $TOTAL_CODES error codes in metadata.json"
echo ""

# Directories to search for tests
TEST_DIRS=(
    "$PROJECT_DIR/tests"
    "$PROJECT_DIR/src"
)

COVERED=()
UNCOVERED=()

for code in $ERROR_CODES; do
    found=false

    # Search in test files
    for dir in "${TEST_DIRS[@]}"; do
        if [[ -d "$dir" ]]; then
            # Look for the error code in .rs files
            if grep -rq "ErrorCode::$code\|$code" "$dir" --include="*.rs" 2>/dev/null; then
                found=true
                break
            fi
        fi
    done

    if $found; then
        COVERED+=("$code")
        if $VERBOSE; then
            echo -e "  ${GREEN}✓${NC} $code"
        fi
    else
        UNCOVERED+=("$code")
        if $VERBOSE; then
            echo -e "  ${RED}✗${NC} $code"
        fi
    fi
done

echo ""
echo -e "${BLUE}=== Coverage Summary ===${NC}"
echo ""

COVERED_COUNT=${#COVERED[@]}
UNCOVERED_COUNT=${#UNCOVERED[@]}
PERCENTAGE=$((COVERED_COUNT * 100 / TOTAL_CODES))

echo -e "Covered:   ${GREEN}$COVERED_COUNT${NC} / $TOTAL_CODES ($PERCENTAGE%)"
echo -e "Uncovered: ${RED}$UNCOVERED_COUNT${NC} / $TOTAL_CODES"

if [[ $UNCOVERED_COUNT -gt 0 ]]; then
    echo ""
    echo -e "${YELLOW}Uncovered error codes:${NC}"
    for code in "${UNCOVERED[@]}"; do
        # Get the error code number from metadata
        CODE_NUM=$(jq -r ".errors[] | select(.name == \"$code\") | .code" "$METADATA_FILE")
        echo "  - $code (E$CODE_NUM)"
    done
    echo ""
    echo -e "${YELLOW}Note: Some error codes may be intentionally deferred (E2xx, E5xx, E6xx, E7xx).${NC}"
    echo "These represent features not yet implemented in the Rust oracle."
fi

# Categorize uncovered codes
DEFERRED_PREFIXES=("E2" "E5" "E6" "E7")  # Registry, Chain, Crypto, Tar
REQUIRED_UNCOVERED=()

for code in "${UNCOVERED[@]}"; do
    CODE_NUM=$(jq -r ".errors[] | select(.name == \"$code\") | .code" "$METADATA_FILE")
    is_deferred=false
    for prefix in "${DEFERRED_PREFIXES[@]}"; do
        if [[ "E$CODE_NUM" == "$prefix"* ]]; then
            is_deferred=true
            break
        fi
    done
    if ! $is_deferred; then
        REQUIRED_UNCOVERED+=("$code")
    fi
done

REQUIRED_UNCOVERED_COUNT=${#REQUIRED_UNCOVERED[@]}

echo ""
if [[ $REQUIRED_UNCOVERED_COUNT -gt 0 ]]; then
    echo -e "${RED}=== FAIL: $REQUIRED_UNCOVERED_COUNT required error codes are not covered ===${NC}"
    echo ""
    echo "Required uncovered codes (E1xx, E3xx, E4xx):"
    for code in "${REQUIRED_UNCOVERED[@]}"; do
        CODE_NUM=$(jq -r ".errors[] | select(.name == \"$code\") | .code" "$METADATA_FILE")
        echo "  - $code (E$CODE_NUM)"
    done
    exit 1
else
    echo -e "${GREEN}=== PASS: All required error codes are covered ===${NC}"
    if [[ $UNCOVERED_COUNT -gt 0 ]]; then
        echo "(${UNCOVERED_COUNT} deferred error codes remain uncovered)"
    fi
    exit 0
fi
