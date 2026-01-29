#!/bin/bash
# Self-healing wrapper that runs the autonomous proof system forever
# This script runs in tmux and restarts the Python process if it dies

cd /home/ubuntu/hodge
export PATH="/home/ubuntu/.elan/bin:$PATH"
export ANTHROPIC_API_KEY="${ANTHROPIC_API_KEY}"

LOG_DIR="/home/ubuntu/hodge/autonomous_logs"
mkdir -p "$LOG_DIR"

echo "$(date): Starting autonomous proof system (run_forever wrapper)" | tee -a "$LOG_DIR/supervisor.log"

while true; do
    echo "$(date): Launching autonomous_proof_complete.py" | tee -a "$LOG_DIR/supervisor.log"
    
    python3 /home/ubuntu/hodge/scripts/agents/autonomous_proof_complete.py 2>&1 | tee -a "$LOG_DIR/output.log"
    
    EXIT_CODE=$?
    echo "$(date): Process exited with code $EXIT_CODE" | tee -a "$LOG_DIR/supervisor.log"
    
    # Check if we should stop (exit code 0 means proof complete)
    if [ $EXIT_CODE -eq 0 ]; then
        echo "$(date): Proof complete! Stopping." | tee -a "$LOG_DIR/supervisor.log"
        break
    fi
    
    # Wait before restarting
    echo "$(date): Restarting in 30 seconds..." | tee -a "$LOG_DIR/supervisor.log"
    sleep 30
done

echo "$(date): run_forever.sh exiting" | tee -a "$LOG_DIR/supervisor.log"
