#!/bin/bash
# One-command setup for the Hodge Conjecture autonomous agent server.
#
# Run on your server:
#   curl -fsSL https://raw.githubusercontent.com/jonwashburn/hodge/main/scripts/setup_server.sh | bash
#
# Or after cloning:
#   ./scripts/setup_server.sh
#
# Prerequisites: Ubuntu/Debian server with root access.
# This script installs Claude Code, Lean 4, clones the repo, and starts the agent loop.

set -euo pipefail

echo "============================================"
echo "Hodge Conjecture Agent Server Setup"
echo "============================================"

# --- Configuration ---
GITHUB_TOKEN="${GITHUB_TOKEN:-}"
ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY:-}"
BRANCH="main"
WORKDIR="/root/hodge"
NUM_AGENTS="${NUM_AGENTS:-1}"
MODEL="${MODEL:-claude-opus-4-6}"

if [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "ERROR: Set ANTHROPIC_API_KEY environment variable"
    echo "  export ANTHROPIC_API_KEY=sk-ant-..."
    echo "  ./scripts/setup_server.sh"
    exit 1
fi

if [ -z "$GITHUB_TOKEN" ]; then
    echo "WARNING: GITHUB_TOKEN not set. Agents won't be able to push."
    echo "  export GITHUB_TOKEN=ghp_..."
fi

# --- Install dependencies ---
echo "[1/6] Installing dependencies..."
apt-get update -qq
apt-get install -y -qq curl git nodejs npm > /dev/null 2>&1

# --- Install Claude Code ---
echo "[2/6] Installing Claude Code..."
if ! command -v claude &> /dev/null; then
    npm install -g @anthropic-ai/claude-code
fi
claude --version

# --- Install Lean 4 (elan) ---
echo "[3/6] Installing Lean 4..."
if [ ! -f "$HOME/.elan/bin/lake" ]; then
    curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | bash -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

# --- Clone repo ---
echo "[4/6] Cloning repository..."
if [ -d "$WORKDIR" ]; then
    cd "$WORKDIR"
    git pull origin "$BRANCH" --no-edit || true
else
    if [ -n "$GITHUB_TOKEN" ]; then
        git clone "https://${GITHUB_TOKEN}@github.com/jonwashburn/hodge.git" "$WORKDIR"
    else
        git clone "https://github.com/jonwashburn/hodge.git" "$WORKDIR"
    fi
    cd "$WORKDIR"
fi
git checkout "$BRANCH"

# --- Configure git for agents ---
git config user.name "hodge-agent"
git config user.email "agent@hodge.lean"
if [ -n "$GITHUB_TOKEN" ]; then
    git remote set-url origin "https://${GITHUB_TOKEN}@github.com/jonwashburn/hodge.git"
fi

# --- Fetch Mathlib cache ---
echo "[5/6] Fetching Mathlib cache (this takes a while)..."
lake exe cache get 2>&1 | tail -3

# --- Create agent loop systemd service ---
echo "[6/6] Setting up agent loop..."

mkdir -p /root/hodge/agent_logs
mkdir -p /root/hodge/current_tasks

cat > /etc/systemd/system/hodge-agent.service << SYSTEMD
[Unit]
Description=Hodge Conjecture Autonomous Agent
After=network.target

[Service]
Type=simple
WorkingDirectory=$WORKDIR
Environment="PATH=$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin"
Environment="ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY"
Environment="GITHUB_TOKEN=$GITHUB_TOKEN"
Environment="HOME=/root"
ExecStart=/bin/bash $WORKDIR/scripts/agent_loop.sh --agents $NUM_AGENTS --model $MODEL
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
SYSTEMD

systemctl daemon-reload
systemctl enable hodge-agent
systemctl start hodge-agent

echo ""
echo "============================================"
echo "Setup complete!"
echo "============================================"
echo ""
echo "Agent loop is running as systemd service."
echo "  Status:  systemctl status hodge-agent"
echo "  Logs:    journalctl -u hodge-agent -f"
echo "  Stop:    systemctl stop hodge-agent"
echo "  Restart: systemctl restart hodge-agent"
echo ""
echo "Agent session logs: $WORKDIR/agent_logs/"
echo ""
