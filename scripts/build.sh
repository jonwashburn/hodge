#!/bin/bash
# Efficient build script - avoids rebuilding Mathlib from source

set -e

cd "$(dirname "$0")/.."

echo "📦 Fetching Mathlib cache (pre-compiled binaries)..."
lake exe cache get

echo ""
echo "🔨 Building project (your code only)..."
lake build

echo ""
echo "✅ Build complete!"
