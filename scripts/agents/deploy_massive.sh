#!/bin/bash
# Deploy Massive Parallel Coordinator to Lambda Labs B200
# Usage: ./deploy_massive.sh YOUR_API_KEY

set -e

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
LOCAL_HODGE="$(dirname "$0")/../.."
REMOTE_HODGE="/home/ubuntu/hodge"

echo "=== MASSIVE PARALLEL DEPLOYMENT ==="
echo "Server: $SERVER"
echo "Max agents: 25"

# Get API key
API_KEY="${1:-$ANTHROPIC_API_KEY}"
if [ -z "$API_KEY" ]; then
    echo "ERROR: No ANTHROPIC_API_KEY provided"
    echo "Usage: ./deploy_massive.sh YOUR_API_KEY"
    exit 1
fi

# Sync codebase
echo ""
echo "=== Syncing codebase ==="
rsync -avz --progress \
    -e "ssh -i $SSH_KEY" \
    --exclude '.lake' \
    --exclude '.git' \
    --exclude 'build' \
    --exclude '*.olean' \
    --exclude '.cache' \
    "$LOCAL_HODGE/" \
    "$SERVER:$REMOTE_HODGE/"

# Setup and install deps
echo ""
echo "=== Setting up server ==="
ssh -i "$SSH_KEY" "$SERVER" << REMOTE_SETUP
cd $REMOTE_HODGE

# Store API key securely
echo '$API_KEY' > ~/.anthropic_api_key
chmod 600 ~/.anthropic_api_key

# Install Python deps if needed
pip3 install aiohttp --quiet 2>/dev/null || pip install aiohttp --quiet

# Make scripts executable
chmod +x scripts/agents/*.py scripts/agents/*.sh

echo "Setup complete"
REMOTE_SETUP

# Start coordinator
echo ""
echo "=== Starting Massive Parallel Coordinator ==="
ssh -i "$SSH_KEY" "$SERVER" << REMOTE_START
cd $REMOTE_HODGE

# Kill any existing coordinator
pkill -f "massive_parallel_coordinator.py" 2>/dev/null || true

# Create log directory
mkdir -p massive_parallel_logs

# Start coordinator in background
nohup python3 scripts/agents/massive_parallel_coordinator.py > massive_parallel.log 2>&1 &
echo "Coordinator PID: \$!"

sleep 2
echo ""
echo "Initial log output:"
tail -20 massive_parallel.log
REMOTE_START

echo ""
echo "=== Deployment Complete ==="
echo ""
echo "Monitor with:"
echo "  ssh -i $SSH_KEY $SERVER 'tail -f $REMOTE_HODGE/massive_parallel.log'"
echo ""
echo "Check status:"
echo "  ssh -i $SSH_KEY $SERVER 'cd $REMOTE_HODGE && python3 scripts/agents/massive_parallel_coordinator.py status'"
echo ""
echo "View individual agent logs:"
echo "  ssh -i $SSH_KEY $SERVER 'ls -la $REMOTE_HODGE/massive_parallel_logs/'"
