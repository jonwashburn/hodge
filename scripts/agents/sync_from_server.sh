#!/bin/bash
# Sync completed work from the Lambda server back to local machine
# Run this anytime to get the latest progress

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
REMOTE="/home/ubuntu/hodge"
LOCAL="$(dirname "$0")/../.."

echo "=== Syncing from Lambda server ==="
echo "Remote: $SERVER:$REMOTE"
echo "Local: $LOCAL"
echo ""

# Sync Lean files
rsync -avz --progress \
    -e "ssh -i $SSH_KEY" \
    --include='*.lean' \
    --include='*/' \
    --exclude='*' \
    "$SERVER:$REMOTE/Hodge/" \
    "$LOCAL/Hodge/"

# Sync logs for review
mkdir -p "$LOCAL/server_logs"
rsync -avz \
    -e "ssh -i $SSH_KEY" \
    "$SERVER:$REMOTE/autonomous_logs/" \
    "$LOCAL/server_logs/" 2>/dev/null || true

rsync -avz \
    -e "ssh -i $SSH_KEY" \
    "$SERVER:$REMOTE/*.log" \
    "$LOCAL/server_logs/" 2>/dev/null || true

# Get current status
echo ""
echo "=== Current Status ==="
ssh -i "$SSH_KEY" "$SERVER" "cat $REMOTE/status.txt 2>/dev/null || echo 'No status file'"

echo ""
echo "=== Task Progress ==="
ssh -i "$SSH_KEY" "$SERVER" "python3 $REMOTE/scripts/agents/autonomous_ops.py status 2>/dev/null | head -20"

echo ""
echo "=== Sync Complete ==="
echo "Lean files synced to: $LOCAL/Hodge/"
echo "Logs synced to: $LOCAL/server_logs/"
