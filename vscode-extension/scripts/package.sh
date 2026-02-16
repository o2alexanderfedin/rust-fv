#!/usr/bin/env bash
set -euo pipefail

# Build platform-specific VSIX packages with bundled Z3 binaries

cd "$(dirname "$0")/.."

echo "Building extension for production..."
npm run build

VERSION=$(node -p "require('./package.json').version")
PLATFORMS=("darwin-x64" "darwin-arm64" "linux-x64" "win32-x64")

echo "Creating platform-specific VSIX packages for version $VERSION..."

for PLATFORM in "${PLATFORMS[@]}"; do
  echo ""
  echo "Packaging for $PLATFORM..."

  # Determine Z3 binary name for this platform
  case "$PLATFORM" in
    darwin-x64)
      Z3_BINARY="z3-darwin-x64"
      ;;
    darwin-arm64)
      Z3_BINARY="z3-darwin-arm64"
      ;;
    linux-x64)
      Z3_BINARY="z3-linux-x64"
      ;;
    win32-x64)
      Z3_BINARY="z3-win32-x64.exe"
      ;;
  esac

  # Check if Z3 binary exists
  if [ ! -f "bin/$Z3_BINARY" ]; then
    echo "Warning: bin/$Z3_BINARY not found. Run scripts/download-z3.sh first."
    echo "Skipping $PLATFORM..."
    continue
  fi

  # Package with vsce
  npx vsce package --target "$PLATFORM" --out "rust-fv-${PLATFORM}-${VERSION}.vsix"

  echo "✓ Created rust-fv-${PLATFORM}-${VERSION}.vsix"
done

echo ""
echo "Building universal VSIX (no bundled Z3)..."
# Create a universal VSIX without Z3 for users who have Z3 installed
# Note: We temporarily move bin/ to avoid including it
if [ -d "bin" ]; then
  mv bin bin.backup
fi
npx vsce package --out "rust-fv-universal-${VERSION}.vsix"
echo "✓ Created rust-fv-universal-${VERSION}.vsix"
if [ -d "bin.backup" ]; then
  mv bin.backup bin
fi

echo ""
echo "All VSIX packages created successfully!"
ls -lh *.vsix
