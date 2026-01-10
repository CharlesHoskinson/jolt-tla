# Makefile for Jolt Oracle Rust implementation

.PHONY: all build test clean release release-musl release-dist fmt clippy check audit help

# Default target
all: build

# Build debug binary
build:
	cargo build

# Run all tests
test:
	cargo test --all-features

# Clean build artifacts
clean:
	cargo clean

# Build release binary (native platform)
release:
	cargo build --release

# Build Linux x86_64 musl static binary
# Requires: rustup target add x86_64-unknown-linux-musl
# Requires: musl-tools package (apt-get install musl-tools)
release-musl:
	cargo build --release --target x86_64-unknown-linux-musl

# Build distribution binary (stripped, optimized)
release-dist:
	cargo build --profile release-dist

# Build distribution binary for musl
release-dist-musl:
	cargo build --profile release-dist --target x86_64-unknown-linux-musl

# Format code
fmt:
	cargo fmt

# Run clippy lints
clippy:
	cargo clippy --all-targets --all-features -- -D warnings

# Run all checks (fmt, clippy, test)
check: fmt clippy test

# Security audit
audit:
	cargo audit

# Check error code coverage
error-coverage:
	./scripts/check-error-coverage.sh

# Check error code coverage (verbose)
error-coverage-verbose:
	./scripts/check-error-coverage.sh --verbose

# Install musl target (run once)
install-musl-target:
	rustup target add x86_64-unknown-linux-musl

# Install macOS ARM64 target (for cross-compilation from x86)
install-macos-target:
	rustup target add aarch64-apple-darwin

# Show binary size
size:
	@echo "Debug binary:"
	@ls -lh target/debug/oracle 2>/dev/null || echo "  Not built"
	@echo "Release binary:"
	@ls -lh target/release/oracle 2>/dev/null || echo "  Not built"
	@echo "Musl binary:"
	@ls -lh target/x86_64-unknown-linux-musl/release/oracle 2>/dev/null || echo "  Not built"

# Verify musl binary is statically linked
verify-static:
	@echo "Checking if musl binary is statically linked..."
	@file target/x86_64-unknown-linux-musl/release/oracle
	@ldd target/x86_64-unknown-linux-musl/release/oracle 2>&1 || true

help:
	@echo "Jolt Oracle Build Targets:"
	@echo ""
	@echo "  build          - Build debug binary"
	@echo "  test           - Run all tests"
	@echo "  release        - Build release binary (native)"
	@echo "  release-musl   - Build Linux musl static binary"
	@echo "  release-dist   - Build stripped distribution binary"
	@echo "  fmt            - Format code"
	@echo "  clippy         - Run clippy lints"
	@echo "  check          - Run fmt, clippy, and tests"
	@echo "  audit          - Run cargo audit"
	@echo "  error-coverage - Check error code test coverage"
	@echo "  clean          - Clean build artifacts"
	@echo ""
	@echo "Setup targets:"
	@echo "  install-musl-target  - Install musl target"
	@echo "  install-macos-target - Install macOS ARM64 target"
	@echo ""
	@echo "Info targets:"
	@echo "  size           - Show binary sizes"
	@echo "  verify-static  - Verify musl binary is static"
