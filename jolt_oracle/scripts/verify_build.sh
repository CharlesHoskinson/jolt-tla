#!/bin/bash
# Jolt Oracle Reproducible Build Verification
# This script records build metadata and computes artifact hashes

set -e

echo "=== Jolt Oracle Build Verification ==="
echo ""

# Get script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

cd "$PROJECT_DIR"

# Record environment
echo "Recording build environment..."
echo ""

# Git info
GIT_COMMIT=$(git rev-parse HEAD 2>/dev/null || echo "not-a-git-repo")
GIT_BRANCH=$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo "unknown")
GIT_DIRTY=$(git diff --quiet 2>/dev/null && echo "clean" || echo "dirty")

# Lean info
LEAN_VERSION=$(cat lean-toolchain 2>/dev/null || echo "unknown")
LAKE_VERSION=$(lake --version 2>/dev/null | head -1 || echo "unknown")

# Timestamp
BUILD_TIME=$(date -u +"%Y-%m-%dT%H:%M:%SZ")

# Create manifest
MANIFEST_FILE="build_manifest.json"

echo "{"
echo "  \"build_time\": \"$BUILD_TIME\","
echo "  \"git\": {"
echo "    \"commit\": \"$GIT_COMMIT\","
echo "    \"branch\": \"$GIT_BRANCH\","
echo "    \"status\": \"$GIT_DIRTY\""
echo "  },"
echo "  \"lean\": {"
echo "    \"toolchain\": \"$LEAN_VERSION\","
echo "    \"lake_version\": \"$LAKE_VERSION\""
echo "  },"

# Build the project
echo ""
echo "Building project..."
lake build 2>&1 || {
    echo "Build failed!"
    exit 1
}

# Compute hashes
echo ""
echo "Computing artifact hashes..."

ORACLE_BIN=".lake/build/bin/oracle"
TEST_BIN=".lake/build/bin/test"

if [ -f "$ORACLE_BIN" ]; then
    ORACLE_HASH=$(sha256sum "$ORACLE_BIN" | cut -d' ' -f1)
    ORACLE_SIZE=$(stat -c%s "$ORACLE_BIN" 2>/dev/null || stat -f%z "$ORACLE_BIN")
else
    ORACLE_HASH="not-found"
    ORACLE_SIZE=0
fi

if [ -f "$TEST_BIN" ]; then
    TEST_HASH=$(sha256sum "$TEST_BIN" | cut -d' ' -f1)
    TEST_SIZE=$(stat -c%s "$TEST_BIN" 2>/dev/null || stat -f%z "$TEST_BIN")
else
    TEST_HASH="not-found"
    TEST_SIZE=0
fi

echo "  \"artifacts\": {"
echo "    \"oracle\": {"
echo "      \"path\": \"$ORACLE_BIN\","
echo "      \"sha256\": \"$ORACLE_HASH\","
echo "      \"size\": $ORACLE_SIZE"
echo "    },"
echo "    \"test\": {"
echo "      \"path\": \"$TEST_BIN\","
echo "      \"sha256\": \"$TEST_HASH\","
echo "      \"size\": $TEST_SIZE"
echo "    }"
echo "  }"
echo "}"

# Write manifest file
cat > "$MANIFEST_FILE" << EOF
{
  "build_time": "$BUILD_TIME",
  "git": {
    "commit": "$GIT_COMMIT",
    "branch": "$GIT_BRANCH",
    "status": "$GIT_DIRTY"
  },
  "lean": {
    "toolchain": "$LEAN_VERSION",
    "lake_version": "$LAKE_VERSION"
  },
  "artifacts": {
    "oracle": {
      "path": "$ORACLE_BIN",
      "sha256": "$ORACLE_HASH",
      "size": $ORACLE_SIZE
    },
    "test": {
      "path": "$TEST_BIN",
      "sha256": "$TEST_HASH",
      "size": $TEST_SIZE
    }
  }
}
EOF

echo ""
echo "Build manifest written to: $MANIFEST_FILE"
echo ""

# Run tests
echo "Running tests..."
lake exe test 2>&1 || {
    echo "Tests failed!"
    exit 1
}

echo ""
echo "=== Build Verification Complete ==="
echo "Oracle SHA256: $ORACLE_HASH"
echo "Test SHA256: $TEST_HASH"
