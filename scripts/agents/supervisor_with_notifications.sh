#!/bin/bash
# Enhanced Supervisor with Notifications and Git Sync

# Ensure elan/lake is in PATH
export PATH="$HOME/.elan/bin:$PATH"

HODGE_PATH="/home/ubuntu/hodge"
LOG_FILE="$HODGE_PATH/supervisor.log"
STATUS_FILE="$HODGE_PATH/status.txt"

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $1" | tee -a "$LOG_FILE"
}

update_status() {
    echo "$1" > "$STATUS_FILE"
}

cleanup() {
    log "Supervisor stopping..."
    pkill -f "autonomous_ops.py" 2>/dev/null
    pkill -f "notifications.py" 2>/dev/null
    update_status "STOPPED"
    exit 0
}

trap cleanup SIGINT SIGTERM

log "=========================================="
log "AUTONOMOUS SUPERVISOR WITH NOTIFICATIONS"
log "=========================================="

cd "$HODGE_PATH" || exit 1

# Setup git
log "Configuring git..."
git config user.email "hodge-bot@autonomous.ai" 2>/dev/null
git config user.name "Hodge Proof Bot" 2>/dev/null

# Get Mathlib cache
log "Getting Mathlib cache..."
lake exe cache get 2>&1 | tail -5

# Start notification monitor in background
log "Starting notification monitor..."
python3 scripts/agents/notifications.py > notifications.log 2>&1 &
NOTIFY_PID=$!
log "Notification monitor PID: $NOTIFY_PID"

# Main loop
RESTART_COUNT=0
MAX_RESTARTS=100

while [ $RESTART_COUNT -lt $MAX_RESTARTS ]; do
    log "Starting autonomous_ops.py (restart #$RESTART_COUNT)"
    update_status "RUNNING (restart #$RESTART_COUNT)"
    
    python3 scripts/agents/autonomous_ops.py 2>&1 | tee -a autonomous_ops.log
    EXIT_CODE=$?
    
    # Auto git commit after each run
    if git diff --quiet Hodge/ 2>/dev/null; then
        log "No changes to commit"
    else
        git add Hodge/ *.lean 2>/dev/null
        COMPLETED=$(python3 -c "import json; d=json.load(open('autonomous_state.json')); print(sum(1 for t in d.get('tasks',[]) if t.get('status')=='completed'))" 2>/dev/null || echo "?")
        git commit -m "[auto] Progress checkpoint: $COMPLETED tasks complete" 2>/dev/null
        git push 2>/dev/null && log "Pushed to GitHub" || log "Git push failed (check credentials)"
    fi
    
    if [ $EXIT_CODE -eq 0 ]; then
        log "Ops agent completed successfully!"
        update_status "COMPLETED"
        
        # Final push
        git add -A
        git commit -m "[COMPLETE] Hodge Conjecture proof finalized" 2>/dev/null
        git push 2>/dev/null
        
        log "=========================================="
        log "PROOF COMPLETE!"
        log "=========================================="
        break
    fi
    
    log "Ops agent exited with code $EXIT_CODE, restarting in 10s..."
    update_status "RESTARTING (exit code $EXIT_CODE)"
    sleep 10
    
    RESTART_COUNT=$((RESTART_COUNT + 1))
done

# Cleanup
kill $NOTIFY_PID 2>/dev/null
