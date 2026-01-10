#!/bin/bash
# Run corpus conformance tests.
#
# This script runs all test vectors from corpus.json against the Rust
# implementation and reports pass/fail status.
#
# Exit codes:
#   0 - All tests passed
#   1 - Some tests failed
#   2 - Script error
#
# Usage:
#   ./scripts/run-corpus.sh [--verbose]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
CORPUS_FILE="$PROJECT_DIR/../jolt_oracle/corpus/corpus.json"

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

echo -e "${BLUE}=== Corpus Conformance Tests ===${NC}"
echo ""

# Check corpus file exists
if [[ ! -f "$CORPUS_FILE" ]]; then
    echo -e "${RED}Error: corpus.json not found at $CORPUS_FILE${NC}"
    echo ""
    echo "Generate it by running:"
    echo "  cd jolt_oracle && lake exe oracle generate-corpus > corpus/corpus.json"
    exit 2
fi

# Get corpus info
if command -v jq &> /dev/null; then
    VECTOR_COUNT=$(jq '.vectors | length' "$CORPUS_FILE")
    FORMAT_VERSION=$(jq -r '.manifest.format_version' "$CORPUS_FILE")
    echo "Corpus: $FORMAT_VERSION with $VECTOR_COUNT vectors"
    echo ""
fi

# Run the corpus tests
echo "Running corpus conformance tests..."
echo ""

cd "$PROJECT_DIR"

if $VERBOSE; then
    cargo test --test corpus_conformance -- --nocapture 2>&1
    EXIT_CODE=$?
else
    OUTPUT=$(cargo test --test corpus_conformance 2>&1)
    EXIT_CODE=$?

    # Extract results
    if echo "$OUTPUT" | grep -q "test result:"; then
        RESULT_LINE=$(echo "$OUTPUT" | grep "test result:")
        echo "$RESULT_LINE"
    fi
fi

echo ""

if [[ $EXIT_CODE -eq 0 ]]; then
    echo -e "${GREEN}=== PASS: All corpus tests passed ===${NC}"
else
    echo -e "${RED}=== FAIL: Some corpus tests failed ===${NC}"
    if ! $VERBOSE; then
        echo ""
        echo "Run with --verbose for details:"
        echo "  ./scripts/run-corpus.sh --verbose"
    fi
fi

exit $EXIT_CODE
