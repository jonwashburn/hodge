#!/bin/bash
# =============================================================================
# deploy_agents.sh — One-command deployment of Hodge proof agents
# =============================================================================
#
# Run this FROM YOUR MAC:
#
#   chmod +x scripts/deploy_agents.sh
#   ./scripts/deploy_agents.sh
#
# Prerequisites:
#   - SSH key at ~/Projects/straight-shot/lambda-b200-private-key
#   - Server at 129.146.121.60
#   - A FRESH Anthropic API key (rotate the one you shared in chat!)
#
# What this does:
#   1. SSHs into the server
#   2. Installs Docker, Git, Node, elan (Lean)
#   3. Clones the repo
#   4. Builds the agent container
#   5. Launches N agents in parallel
#   6. Sets up a tmux session for monitoring
# =============================================================================

set -euo pipefail

# ─── Configuration ───────────────────────────────────────────────────────────
SERVER="129.146.121.60"
SSH_KEY="$HOME/Projects/straight-shot/lambda-b200-private-key"
SSH_USER="${SSH_USER:-ubuntu}"  # change to 'root' or 'opc' if needed
NUM_AGENTS="${NUM_AGENTS:-8}"   # 8 agents, no budget constraints
MODEL="claude-opus-4-6"
BRANCH="claude/hodge-conjecture-proof-VSeH8"
REPO_URL="https://github.com/jonwashburn/hodge.git"

# ─── Prompt for API key ─────────────────────────────────────────────────────
echo "============================================"
echo "  Hodge Proof — Agent Team Deployment"
echo "============================================"
echo ""
echo "IMPORTANT: Generate a FRESH API key at https://console.anthropic.com/"
echo "           (The key shared in chat should be rotated!)"
echo ""
read -sp "Enter your Anthropic API key: " ANTHROPIC_API_KEY
echo ""

if [[ -z "$ANTHROPIC_API_KEY" ]]; then
    echo "ERROR: API key is required."
    exit 1
fi

# ─── SSH helper ──────────────────────────────────────────────────────────────
SSH_CMD="ssh -i $SSH_KEY -o StrictHostKeyChecking=no ${SSH_USER}@${SERVER}"
SCP_CMD="scp -i $SSH_KEY -o StrictHostKeyChecking=no"

echo ""
echo "Testing SSH connection..."
$SSH_CMD "echo 'Connected to $(hostname) as $(whoami)'" || {
    echo "SSH failed. Try SSH_USER=root or SSH_USER=opc:"
    echo "  SSH_USER=root ./scripts/deploy_agents.sh"
    exit 1
}

echo "Connection OK. Deploying..."

# ─── Step 1: Install dependencies on server ──────────────────────────────────
echo ""
echo "=== Step 1/5: Installing dependencies ==="
$SSH_CMD "bash -s" <<'REMOTE_DEPS'
set -e

# Docker
if ! command -v docker &>/dev/null; then
    echo "Installing Docker..."
    curl -fsSL https://get.docker.com | sh
    sudo usermod -aG docker $USER || true
fi

# Git
if ! command -v git &>/dev/null; then
    sudo apt-get update && sudo apt-get install -y git
fi

# Node.js (for Claude CLI)
if ! command -v node &>/dev/null; then
    echo "Installing Node.js..."
    curl -fsSL https://deb.nodesource.com/setup_20.x | sudo -E bash -
    sudo apt-get install -y nodejs
fi

# tmux for monitoring
sudo apt-get install -y tmux || true

echo "Dependencies installed."
REMOTE_DEPS

# ─── Step 2: Clone repo and set up workspace ─────────────────────────────────
echo ""
echo "=== Step 2/5: Setting up workspace ==="
$SSH_CMD "bash -s" <<REMOTE_REPO
set -e

# Clean workspace
rm -rf ~/hodge-workspace
mkdir -p ~/hodge-workspace

# Clone
cd ~/hodge-workspace
git clone ${REPO_URL} hodge
cd hodge
git checkout ${BRANCH}

# Create bare upstream repo for agent coordination
cd ~/hodge-workspace
git init --bare upstream.git
cd hodge
git remote add upstream ~/hodge-workspace/upstream.git || git remote set-url upstream ~/hodge-workspace/upstream.git
git push upstream ${BRANCH}

echo "Repo cloned and upstream configured."
REMOTE_REPO

# ─── Step 3: Write the agent runner script on server ──────────────────────────
echo ""
echo "=== Step 3/5: Writing agent runner ==="
$SSH_CMD "bash -s" <<'REMOTE_RUNNER'
cat > ~/hodge-workspace/run_agents.sh <<'AGENT_SCRIPT'
#!/bin/bash
# Launches N agents, each in its own tmux window
set -euo pipefail

NUM_AGENTS=${1:-8}
MODEL=${2:-claude-opus-4-6}
BRANCH="claude/hodge-conjecture-proof-VSeH8"
WORKSPACE=~/hodge-workspace

echo "Launching ${NUM_AGENTS} agents..."

# Create tmux session
tmux new-session -d -s hodge 2>/dev/null || true

for i in $(seq 1 $NUM_AGENTS); do
    AGENT_DIR="${WORKSPACE}/agent_${i}"

    # Create agent workspace (clone from upstream)
    rm -rf "$AGENT_DIR"
    git clone "${WORKSPACE}/upstream.git" "$AGENT_DIR"
    cd "$AGENT_DIR"
    git checkout "$BRANCH"

    # Create the agent loop for this agent
    cat > "${AGENT_DIR}/run.sh" <<INNER_EOF
#!/bin/bash
set -uo pipefail
cd ${AGENT_DIR}

# Install Lean toolchain if needed
if command -v elan &>/dev/null; then
    elan install \$(cat lean-toolchain) 2>/dev/null || true
fi

ITERATION=0
while true; do
    ITERATION=\$((ITERATION + 1))
    COMMIT=\$(git rev-parse --short=6 HEAD)
    TIMESTAMP=\$(date +%Y%m%d_%H%M%S)
    LOG="${AGENT_DIR}/logs/session_\${TIMESTAMP}_\${COMMIT}.log"
    mkdir -p "${AGENT_DIR}/logs"

    echo "[Agent ${i}] Iteration \${ITERATION} at \${COMMIT}..."

    # Pull latest from upstream
    git pull upstream ${BRANCH} --no-edit 2>/dev/null || true

    # Run Claude
    claude --dangerously-skip-permissions \
           -p "\$(cat AGENT_PROMPT.md)" \
           --model ${MODEL} \
           &> "\${LOG}" || true

    # Push any changes
    git add -A
    git commit -m "[agent-${i}] Iteration \${ITERATION}" --allow-empty 2>/dev/null || true
    git push upstream ${BRANCH} 2>/dev/null || true

    echo "[Agent ${i}] Session done. Sleeping 10s..."
    sleep 10
done
INNER_EOF
    chmod +x "${AGENT_DIR}/run.sh"

    # Launch in tmux window
    if [ "$i" -eq 1 ]; then
        tmux rename-window -t hodge "agent-1"
        tmux send-keys -t hodge "cd ${AGENT_DIR} && ./run.sh" C-m
    else
        tmux new-window -t hodge -n "agent-${i}"
        tmux send-keys -t hodge:agent-${i} "cd ${AGENT_DIR} && ./run.sh" C-m
    fi

    echo "  Launched agent ${i}"
    sleep 3
done

# Add a monitoring window
tmux new-window -t hodge -n "monitor"
tmux send-keys -t hodge:monitor "watch -n 30 'cd ~/hodge-workspace/hodge && git pull upstream ${BRANCH} --no-edit 2>/dev/null; ./scripts/verify_progress.sh 2>/dev/null'" C-m

echo ""
echo "All ${NUM_AGENTS} agents launched in tmux session 'hodge'."
echo "Attach with: tmux attach -t hodge"
echo "Monitor progress in the 'monitor' tab."
AGENT_SCRIPT
chmod +x ~/hodge-workspace/run_agents.sh
echo "Agent runner written."
REMOTE_RUNNER

# ─── Step 4: Install Claude CLI and elan on server ────────────────────────────
echo ""
echo "=== Step 4/5: Installing Claude CLI and Lean ==="
$SSH_CMD "bash -s" <<'REMOTE_TOOLS'
set -e

# Claude CLI
if ! command -v claude &>/dev/null; then
    echo "Installing Claude Code CLI..."
    sudo npm install -g @anthropic-ai/claude-code
fi

# elan (Lean version manager)
if ! command -v elan &>/dev/null; then
    echo "Installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | bash -s -- -y --default-toolchain none
    echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.bashrc
    export PATH="$HOME/.elan/bin:$PATH"
fi

export PATH="$HOME/.elan/bin:$PATH"

# Pre-build Lean and fetch Mathlib cache
cd ~/hodge-workspace/hodge
elan install $(cat lean-toolchain) 2>/dev/null || true
lake exe cache get 2>/dev/null || echo "Cache fetch skipped (may need manual run)"

echo "Tools installed."
REMOTE_TOOLS

# ─── Step 5: Set API key and launch ──────────────────────────────────────────
echo ""
echo "=== Step 5/5: Setting API key and launching agents ==="
$SSH_CMD "bash -s" <<REMOTE_LAUNCH
set -e

# Store API key for agents
echo "export ANTHROPIC_API_KEY='${ANTHROPIC_API_KEY}'" >> ~/.bashrc
export ANTHROPIC_API_KEY='${ANTHROPIC_API_KEY}'

# Launch agents
export PATH="\$HOME/.elan/bin:\$PATH"
cd ~/hodge-workspace
./run_agents.sh ${NUM_AGENTS} ${MODEL}
REMOTE_LAUNCH

echo ""
echo "============================================"
echo "  DEPLOYMENT COMPLETE"
echo "============================================"
echo ""
echo "  Server:  ${SERVER}"
echo "  Agents:  ${NUM_AGENTS}"
echo "  Model:   ${MODEL}"
echo "  Branch:  ${BRANCH}"
echo ""
echo "  To monitor:"
echo "    ssh -i ${SSH_KEY} ${SSH_USER}@${SERVER} 'tmux attach -t hodge'"
echo ""
echo "  To check progress:"
echo "    ssh -i ${SSH_KEY} ${SSH_USER}@${SERVER} 'cd ~/hodge-workspace/hodge && git pull upstream ${BRANCH} --no-edit && ./scripts/verify_progress.sh'"
echo ""
echo "  To pull results locally:"
echo "    git pull origin ${BRANCH}"
echo ""
echo "  To stop all agents:"
echo "    ssh -i ${SSH_KEY} ${SSH_USER}@${SERVER} 'tmux kill-session -t hodge'"
echo ""
