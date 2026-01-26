#!/bin/bash
# Setup script for Hodge Agent Coordinator on Lambda Labs B200

set -e

echo "=== Hodge Formalization Agent Setup ==="
echo "Server: $(hostname)"
echo "Date: $(date)"

# Update system
sudo apt-get update
sudo apt-get install -y python3-pip git

# Install Python dependencies
pip3 install --user aiohttp anthropic

# Clone/update the hodge repo
HODGE_PATH="/home/ubuntu/hodge"
if [ -d "$HODGE_PATH" ]; then
    echo "Updating existing repo..."
    cd "$HODGE_PATH"
    git pull origin main || true
else
    echo "Cloning hodge repo..."
    git clone https://github.com/jonathanwashburn/hodge.git "$HODGE_PATH" || {
        echo "Repo doesn't exist on GitHub. Creating local copy..."
        mkdir -p "$HODGE_PATH"
    }
fi

# Install elan (Lean version manager)
if ! command -v elan &> /dev/null; then
    echo "Installing elan..."
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
    source ~/.profile
fi

# Add to PATH
export PATH="$HOME/.elan/bin:$HOME/.local/bin:$PATH"

# Setup Lean in the project
if [ -f "$HODGE_PATH/lakefile.lean" ]; then
    cd "$HODGE_PATH"
    echo "Running lake exe cache get..."
    lake exe cache get || echo "Cache get failed, will build from source"
fi

# Create log directory
mkdir -p "$HODGE_PATH/agent_logs"

echo ""
echo "=== Setup Complete ==="
echo "To run the coordinator:"
echo "  export ANTHROPIC_API_KEY='your-key-here'"
echo "  cd $HODGE_PATH"
echo "  python3 scripts/agents/coordinator.py"
echo ""
echo "To check status:"
echo "  python3 scripts/agents/coordinator.py status"
