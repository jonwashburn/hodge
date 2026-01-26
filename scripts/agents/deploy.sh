#!/bin/bash
# Deploy the Hodge Agent Coordinator to Lambda Labs B200
# Usage: ./deploy.sh [ANTHROPIC_API_KEY]

set -e

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
LOCAL_HODGE="$(dirname "$0")/../.."
REMOTE_HODGE="/home/ubuntu/hodge"

echo "=== Deploying Hodge Agent Coordinator ==="

# Check API key
if [ -z "$1" ] && [ -z "$ANTHROPIC_API_KEY" ]; then
    echo "Warning: No ANTHROPIC_API_KEY provided"
    echo "Usage: ./deploy.sh YOUR_API_KEY"
    echo "Or set ANTHROPIC_API_KEY environment variable"
fi

API_KEY="${1:-$ANTHROPIC_API_KEY}"

# Sync the codebase
echo "Syncing codebase to server..."
rsync -avz --progress \
    -e "ssh -i $SSH_KEY" \
    --exclude '.lake' \
    --exclude '.git' \
    --exclude 'build' \
    --exclude '*.olean' \
    --exclude '.cache' \
    "$LOCAL_HODGE/" \
    "$SERVER:$REMOTE_HODGE/"

# Run setup on server
echo "Running server setup..."
ssh -i "$SSH_KEY" "$SERVER" "chmod +x $REMOTE_HODGE/scripts/agents/setup_server.sh && $REMOTE_HODGE/scripts/agents/setup_server.sh"

# Start the coordinator
if [ -n "$API_KEY" ]; then
    echo "Starting coordinator..."
    ssh -i "$SSH_KEY" "$SERVER" "cd $REMOTE_HODGE && nohup env ANTHROPIC_API_KEY='$API_KEY' python3 scripts/agents/coordinator.py > agent_coordinator.log 2>&1 &"
    echo "Coordinator started in background"
    echo ""
    echo "To monitor:"
    echo "  ssh -i $SSH_KEY $SERVER 'tail -f $REMOTE_HODGE/agent_coordinator.log'"
    echo ""
    echo "To check status:"
    echo "  ssh -i $SSH_KEY $SERVER 'cd $REMOTE_HODGE && python3 scripts/agents/coordinator.py status'"
else
    echo ""
    echo "To start manually:"
    echo "  ssh -i $SSH_KEY $SERVER"
    echo "  export ANTHROPIC_API_KEY='your-key'"
    echo "  cd $REMOTE_HODGE && python3 scripts/agents/coordinator.py"
fi
