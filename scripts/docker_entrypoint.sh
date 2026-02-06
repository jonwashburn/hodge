#!/bin/bash
# Docker entrypoint for Hodge autonomous agent
# Clones from /upstream (bare repo), runs agent loop

set -euo pipefail

BRANCH="${BRANCH:-claude/hodge-conjecture-proof-VSeH8}"
MODEL="${MODEL:-claude-opus-4-6}"

echo "=== Hodge Agent Container Starting ==="
echo "Branch: $BRANCH"
echo "Model: $MODEL"

# Clone from upstream bare repo
if [ -d /upstream ]; then
    echo "Cloning from /upstream..."
    git clone /upstream /workspace/hodge
    cd /workspace/hodge
    git checkout "$BRANCH" || git checkout -b "$BRANCH"
else
    echo "ERROR: /upstream not mounted. Mount a bare git repo."
    exit 1
fi

# Install Lean toolchain
echo "Installing Lean toolchain..."
cd /workspace/hodge
elan install $(cat lean-toolchain)

# Fetch Mathlib cache
echo "Fetching Mathlib cache..."
lake exe cache get

# Verify build
echo "Verifying build..."
lake build

echo "Build OK. Starting agent loop..."

# Run the agent loop
exec ./scripts/agent_loop.sh --model "$MODEL"
