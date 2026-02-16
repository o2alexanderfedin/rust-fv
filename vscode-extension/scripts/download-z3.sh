#!/usr/bin/env bash
set -euo pipefail

# Download Z3 binaries for VSCode extension bundling
# This script is for CI/developer use, not end users

Z3_VERSION="4.13.0"
BIN_DIR="$(dirname "$0")/../bin"
mkdir -p "$BIN_DIR"

echo "Downloading Z3 binaries for version $Z3_VERSION..."

# macOS arm64
echo "Downloading Z3 for macOS arm64..."
curl -L "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-arm64-osx-11.0.zip" -o /tmp/z3-darwin-arm64.zip
unzip -q /tmp/z3-darwin-arm64.zip -d /tmp/
cp "/tmp/z3-${Z3_VERSION}-arm64-osx-11.0/bin/z3" "$BIN_DIR/z3-darwin-arm64"
chmod +x "$BIN_DIR/z3-darwin-arm64"
rm -rf /tmp/z3-darwin-arm64.zip "/tmp/z3-${Z3_VERSION}-arm64-osx-11.0"

# macOS x64
echo "Downloading Z3 for macOS x64..."
curl -L "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-osx-11.7.10.zip" -o /tmp/z3-darwin-x64.zip
unzip -q /tmp/z3-darwin-x64.zip -d /tmp/
cp "/tmp/z3-${Z3_VERSION}-x64-osx-11.7.10/bin/z3" "$BIN_DIR/z3-darwin-x64"
chmod +x "$BIN_DIR/z3-darwin-x64"
rm -rf /tmp/z3-darwin-x64.zip "/tmp/z3-${Z3_VERSION}-x64-osx-11.7.10"

# Linux x64
echo "Downloading Z3 for Linux x64..."
curl -L "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-glibc-2.35.zip" -o /tmp/z3-linux-x64.zip
unzip -q /tmp/z3-linux-x64.zip -d /tmp/
cp "/tmp/z3-${Z3_VERSION}-x64-glibc-2.35/bin/z3" "$BIN_DIR/z3-linux-x64"
chmod +x "$BIN_DIR/z3-linux-x64"
rm -rf /tmp/z3-linux-x64.zip "/tmp/z3-${Z3_VERSION}-x64-glibc-2.35"

# Windows x64
echo "Downloading Z3 for Windows x64..."
curl -L "https://github.com/Z3Prover/z3/releases/download/z3-${Z3_VERSION}/z3-${Z3_VERSION}-x64-win.zip" -o /tmp/z3-win32-x64.zip
unzip -q /tmp/z3-win32-x64.zip -d /tmp/
cp "/tmp/z3-${Z3_VERSION}-x64-win/bin/z3.exe" "$BIN_DIR/z3-win32-x64.exe"
rm -rf /tmp/z3-win32-x64.zip "/tmp/z3-${Z3_VERSION}-x64-win"

echo "✓ Z3 binaries downloaded to $BIN_DIR/"
ls -lh "$BIN_DIR/"
