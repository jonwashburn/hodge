#!/bin/bash
# Setup Slack notifications and GitHub sync on the Lambda server
# Usage: ./setup_notifications.sh SLACK_WEBHOOK_URL GITHUB_TOKEN

SERVER="ubuntu@192.222.59.220"
SSH_KEY="$HOME/.ssh/lambda-b200"
REMOTE="/home/ubuntu/hodge"

SLACK_WEBHOOK="$1"
GITHUB_TOKEN="$2"
GITHUB_REPO="${3:-jonathanwashburn/hodge}"  # Default repo

if [ -z "$SLACK_WEBHOOK" ]; then
    echo "Usage: ./setup_notifications.sh SLACK_WEBHOOK_URL [GITHUB_TOKEN] [GITHUB_REPO]"
    echo ""
    echo "SLACK_WEBHOOK_URL: Your Slack incoming webhook URL"
    echo "GITHUB_TOKEN: Personal access token with repo permissions (optional for push)"
    echo "GITHUB_REPO: Repository in format 'owner/repo' (default: jonathanwashburn/hodge)"
    exit 1
fi

echo "=== Setting up notifications and git sync ==="

ssh -i "$SSH_KEY" "$SERVER" << REMOTE_SETUP
cd /home/ubuntu/hodge

# Save Slack webhook
echo '$SLACK_WEBHOOK' > ~/.hodge_slack_webhook
chmod 600 ~/.hodge_slack_webhook
echo "Slack webhook saved"

# Initialize git if needed
if [ ! -d .git ]; then
    git init
    echo "Git initialized"
fi

# Configure git
git config user.email "hodge-bot@autonomous.ai"
git config user.name "Hodge Proof Bot"

# Setup GitHub remote
GITHUB_TOKEN='$GITHUB_TOKEN'
GITHUB_REPO='$GITHUB_REPO'

if [ -n "\$GITHUB_TOKEN" ]; then
    git remote remove origin 2>/dev/null || true
    git remote add origin "https://\${GITHUB_TOKEN}@github.com/\${GITHUB_REPO}.git"
    echo "GitHub remote configured with token"
    
    # Test push
    git fetch origin 2>/dev/null && echo "GitHub connection verified" || echo "Warning: Could not connect to GitHub"
else
    echo "No GitHub token provided - git push will be skipped"
fi

# Test Slack
python3 << 'PYTHON'
import asyncio
import aiohttp

async def test():
    webhook = open('/home/ubuntu/.hodge_slack_webhook').read().strip()
    async with aiohttp.ClientSession() as session:
        await session.post(webhook, json={"text": "🔔 Hodge Proof Bot connected! Notifications enabled."})
        print("Slack test message sent")

asyncio.run(test())
PYTHON

echo ""
echo "Setup complete!"
REMOTE_SETUP

echo ""
echo "=== Next Steps ==="
echo "1. Check your Slack channel for the test message"
echo "2. Restart the supervisor to enable notifications:"
echo "   ssh -i $SSH_KEY $SERVER 'tmux kill-session -t hodge_auto; tmux new-session -d -s hodge_auto \"cd /home/ubuntu/hodge && ./scripts/agents/supervisor_with_notifications.sh\"'"
