#!/bin/bash
# Setup script for cross-compilation targets
# Usage: ./scripts/setup-cross.sh [target]

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
    exit 1
}

# Install musl target and tools
setup_musl() {
    info "Setting up x86_64-unknown-linux-musl target..."

    # Add rustup target
    rustup target add x86_64-unknown-linux-musl

    # Check for musl-gcc
    if command -v musl-gcc &> /dev/null; then
        info "musl-gcc already installed"
    else
        warn "musl-gcc not found. Installing musl-tools..."
        if command -v apt-get &> /dev/null; then
            sudo apt-get update
            sudo apt-get install -y musl-tools
        elif command -v apk &> /dev/null; then
            sudo apk add musl-dev
        elif command -v dnf &> /dev/null; then
            sudo dnf install -y musl-gcc musl-libc-static
        else
            error "Cannot install musl-tools. Please install manually."
        fi
    fi

    info "musl target setup complete!"
}

# Install macOS ARM64 target
setup_macos_arm64() {
    info "Setting up aarch64-apple-darwin target..."
    rustup target add aarch64-apple-darwin
    info "macOS ARM64 target setup complete!"
}

# Install macOS x86_64 target
setup_macos_x64() {
    info "Setting up x86_64-apple-darwin target..."
    rustup target add x86_64-apple-darwin
    info "macOS x86_64 target setup complete!"
}

# Install Windows target
setup_windows() {
    info "Setting up x86_64-pc-windows-gnu target..."
    rustup target add x86_64-pc-windows-gnu

    # Check for mingw
    if ! command -v x86_64-w64-mingw32-gcc &> /dev/null; then
        warn "mingw-w64 not found. Installing..."
        if command -v apt-get &> /dev/null; then
            sudo apt-get update
            sudo apt-get install -y mingw-w64
        else
            warn "Please install mingw-w64 manually for Windows cross-compilation"
        fi
    fi

    info "Windows target setup complete!"
}

# Show available targets
show_targets() {
    echo "Available targets:"
    echo "  musl       - x86_64-unknown-linux-musl (static Linux binary)"
    echo "  macos-arm  - aarch64-apple-darwin (macOS ARM64)"
    echo "  macos-x64  - x86_64-apple-darwin (macOS x86_64)"
    echo "  windows    - x86_64-pc-windows-gnu (Windows)"
    echo "  all        - Install all targets"
    echo ""
    echo "Currently installed targets:"
    rustup target list --installed
}

# Main
case "${1:-help}" in
    musl)
        setup_musl
        ;;
    macos-arm)
        setup_macos_arm64
        ;;
    macos-x64)
        setup_macos_x64
        ;;
    windows)
        setup_windows
        ;;
    all)
        setup_musl
        setup_macos_arm64
        setup_macos_x64
        setup_windows
        ;;
    list|targets)
        show_targets
        ;;
    help|*)
        echo "Usage: $0 <target>"
        echo ""
        show_targets
        ;;
esac
