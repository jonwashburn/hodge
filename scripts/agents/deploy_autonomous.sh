#!/bin/bash
# Deploy and start the fully autonomous Hodge proof system
set -e

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
REMOTE="/home/ubuntu/hodge"

echo "=== DEPLOYING AUTONOMOUS HODGE PROOF SYSTEM ==="

# Sync
echo "Syncing codebase..."
rsync -avz --progress \
    -e "ssh -i $SSH_KEY" \
    --exclude '.lake' --exclude '.git' --exclude 'build' --exclude '*.olean' \
    "$(dirname "$0")/../.." \
    "$SERVER:$REMOTE/"

# Setup and start
echo "Starting autonomous system..."
ssh -i "$SSH_KEY" "$SERVER" << 'REMOTE'
cd /home/ubuntu/hodge

# Kill any existing processes
pkill -f "autonomous_ops.py" 2>/dev/null || true
pkill -f "supervisor.sh" 2>/dev/null || true

# Make executable
chmod +x scripts/agents/*.py scripts/agents/*.sh

# Start supervisor in tmux
tmux kill-session -t hodge_auto 2>/dev/null || true
tmux new-session -d -s hodge_auto "cd /home/ubuntu/hodge && ./scripts/agents/supervisor.sh"

echo "Started in tmux session 'hodge_auto'"
sleep 2

# Show initial output
echo ""
echo "=== Initial Log ==="
tail -20 supervisor.log 2>/dev/null || echo "(no log yet)"
REMOTE

echo ""
echo "=== DEPLOYMENT COMPLETE ==="
echo ""
echo "Monitor:"
echo "  ssh -i $SSH_KEY $SERVER 'tmux attach -t hodge_auto'"
echo ""
echo "Status:"
echo "  ssh -i $SSH_KEY $SERVER 'cat /home/ubuntu/hodge/status.txt'"
echo ""
echo "Logs:"
echo "  ssh -i $SSH_KEY $SERVER 'tail -f /home/ubuntu/hodge/autonomous_ops.log'"
