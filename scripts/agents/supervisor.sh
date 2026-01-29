#!/bin/bash
# Autonomous Supervisor - Keeps the ops agent running forever
# Restarts on crash, logs everything, sends status updates

HODGE_PATH="/home/ubuntu/hodge"
LOG_FILE="$HODGE_PATH/supervisor.log"
STATUS_FILE="$HODGE_PATH/status.txt"

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $1" | tee -a "$LOG_FILE"
}

update_status() {
    echo "$1" > "$STATUS_FILE"
    echo "$(date '+%Y-%m-%d %H:%M:%S'): $1" >> "$STATUS_FILE.history"
}

cleanup() {
    log "Supervisor stopping..."
    pkill -f "autonomous_ops.py" 2>/dev/null
    update_status "STOPPED"
    exit 0
}

trap cleanup SIGINT SIGTERM

log "=========================================="
log "AUTONOMOUS SUPERVISOR STARTING"
log "=========================================="

update_status "STARTING"

# Initial setup
cd "$HODGE_PATH" || exit 1

# Get Mathlib cache once
log "Getting Mathlib cache..."
lake exe cache get 2>&1 | tail -5

# Main supervisor loop
RESTART_COUNT=0
MAX_RESTARTS=100

while [ $RESTART_COUNT -lt $MAX_RESTARTS ]; do
    log "Starting autonomous_ops.py (restart #$RESTART_COUNT)"
    update_status "RUNNING (restart #$RESTART_COUNT)"
    
    # Run the ops agent
    python3 scripts/agents/autonomous_ops.py 2>&1 | tee -a autonomous_ops.log
    EXIT_CODE=$?
    
    if [ $EXIT_CODE -eq 0 ]; then
        log "Ops agent completed successfully!"
        update_status "COMPLETED"
        
        # Final verification
        log "Running final axiom check..."
        lake env lean Hodge/Utils/DependencyCheck.lean 2>&1 | tee -a "$LOG_FILE"
        
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

if [ $RESTART_COUNT -ge $MAX_RESTARTS ]; then
    log "Max restarts reached, stopping"
    update_status "FAILED (max restarts)"
fi
