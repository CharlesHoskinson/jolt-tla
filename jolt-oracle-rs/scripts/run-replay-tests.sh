#!/bin/bash
# Run replay tests and save outputs.
#
# This script runs the oracle binary on all replay test fixtures
# and saves the outputs to a JSON file for cross-platform comparison.
#
# Usage:
#   ./scripts/run-replay-tests.sh <oracle-binary> <output-file>
#
# Example:
#   ./scripts/run-replay-tests.sh ./target/release/oracle replay-linux.json

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
FIXTURES_DIR="$PROJECT_DIR/tests/fixtures/replay"

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <oracle-binary> <output-file>"
    exit 1
fi

ORACLE_BIN="$1"
OUTPUT_FILE="$2"

if [[ ! -x "$ORACLE_BIN" ]]; then
    echo "Error: Oracle binary not found or not executable: $ORACLE_BIN"
    exit 1
fi

# Get oracle version
VERSION=$("$ORACLE_BIN" --version 2>&1 || echo "unknown")

echo "Running replay tests..."
echo "Binary: $ORACLE_BIN"
echo "Version: $VERSION"
echo "Output: $OUTPUT_FILE"
echo ""

# Start JSON output
echo "{" > "$OUTPUT_FILE"
echo "  \"version\": \"$VERSION\"," >> "$OUTPUT_FILE"
echo "  \"platform\": \"$(uname -s)-$(uname -m)\"," >> "$OUTPUT_FILE"
echo "  \"results\": {" >> "$OUTPUT_FILE"

FIRST=true

# Run digest tests
for fixture in "$FIXTURES_DIR"/digest_*.json; do
    if [[ -f "$fixture" ]]; then
        name=$(basename "$fixture" .json)
        echo "  Running: $name"

        # Run oracle and capture output
        output=$("$ORACLE_BIN" digest "$fixture" 2>&1 || true)

        # Escape for JSON
        escaped=$(echo "$output" | sed 's/\\/\\\\/g' | sed 's/"/\\"/g' | tr '\n' ' ')

        if [[ "$FIRST" == "true" ]]; then
            FIRST=false
        else
            echo "," >> "$OUTPUT_FILE"
        fi

        echo -n "    \"$name\": \"$escaped\"" >> "$OUTPUT_FILE"
    fi
done

echo "" >> "$OUTPUT_FILE"
echo "  }" >> "$OUTPUT_FILE"
echo "}" >> "$OUTPUT_FILE"

echo ""
echo "Results saved to: $OUTPUT_FILE"
