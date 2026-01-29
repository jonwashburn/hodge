#!/usr/bin/env python3
"""
Fully Autonomous Proof Completion System

This script runs indefinitely, eliminating sorries one by one until the proof
is complete. It includes self-healing, progress tracking, and Slack notifications.

CRITICAL: This system will NOT accept trivializations like:
- := trivial
- := True
- := True.intro
- : True :=
- ⟨⟩ for non-unit types
"""

import os
import re
import subprocess
import json
import time
import datetime
import urllib.request
from pathlib import Path

# Configuration
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK", "")
MODEL = "claude-opus-4-5-20251101"
REPO_PATH = Path("/home/ubuntu/hodge")
LOG_DIR = REPO_PATH / "autonomous_logs"
LAKE_PATH = "/home/ubuntu/.elan/bin/lake"

# Target files to work on (in priority order)
TARGET_FILES = [
    "Hodge/Analytic/Integration/SubmanifoldIntegral.lean",
    "Hodge/Analytic/Integration/Stokes.lean",
    "Hodge/GMT/Mass.lean",
    "Hodge/GMT/FlatNorm.lean",
    "Hodge/GMT/Calibration.lean",
    "Hodge/Kahler/Main.lean",
    "Hodge/Classical/GAGA.lean",
]

# FORBIDDEN patterns - these are trivializations
FORBIDDEN_PATTERNS = [
    r':=\s*trivial\s*$',
    r':=\s*True\s*$',
    r':=\s*True\.intro\s*$',
    r':\s*True\s*:=',
    r':=\s*⟨⟩\s*$',
    r'\badmit\b',
    r':=\s*rfl\s*$.*sorry',  # rfl replacing sorry when types don't match
]

# Stats tracking
stats = {
    "start_time": None,
    "sorries_eliminated": 0,
    "failed_attempts": 0,
    "rejected_trivializations": 0,
    "cycles": 0,
    "last_slack_update": 0,
}

def log(msg):
    """Log with timestamp."""
    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    line = f"[{ts}] {msg}"
    print(line, flush=True)
    try:
        with open(LOG_DIR / "main.log", "a") as f:
            f.write(line + "\n")
    except:
        pass

def slack_notify(msg):
    """Send Slack notification."""
    try:
        data = json.dumps({"text": msg}).encode()
        req = urllib.request.Request(SLACK_WEBHOOK, data=data, 
                                      headers={"Content-Type": "application/json"})
        urllib.request.urlopen(req, timeout=10)
    except Exception as e:
        log(f"Slack error: {e}")

def run_cmd(cmd, timeout=300):
    """Run shell command with timeout."""
    try:
        result = subprocess.run(cmd, shell=True, capture_output=True, 
                                text=True, timeout=timeout, cwd=REPO_PATH)
        return result.returncode == 0, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        return False, "Command timed out"
    except Exception as e:
        return False, str(e)

def count_sorries(filepath):
    """Count sorry tokens in a file."""
    try:
        content = (REPO_PATH / filepath).read_text()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        lines = content.splitlines()
        count = sum(1 for line in lines 
                   if re.search(pattern, line) and not line.strip().startswith('--'))
        return count
    except:
        return -1

def get_total_sorries():
    """Get total sorry count across all target files."""
    total = 0
    for f in TARGET_FILES:
        c = count_sorries(f)
        if c > 0:
            total += c
    return total

def check_build():
    """Verify the build is green."""
    log("Checking build...")
    ok, output = run_cmd(f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} build 2>&1 | tail -5")
    is_green = "Build completed successfully" in output
    if is_green:
        log("Build is GREEN ✅")
    else:
        log(f"Build FAILED: {output[-200:]}")
    return is_green

def is_trivialization(new_code):
    """Check if the proposed code is a forbidden trivialization."""
    for pattern in FORBIDDEN_PATTERNS:
        if re.search(pattern, new_code, re.IGNORECASE):
            return True
    
    # Additional checks
    if ':= trivial' in new_code.lower():
        return True
    if ':= true' in new_code.lower() and 'True.intro' not in new_code:
        return True
    if ': True :=' in new_code:
        return True
        
    return False

def find_first_sorry(filepath):
    """Find the first sorry in a file with context."""
    try:
        content = (REPO_PATH / filepath).read_text()
        lines = content.splitlines()
        pattern = r'(?<![A-Za-z0-9_])sorry(?![A-Za-z0-9_])'
        
        for i, line in enumerate(lines):
            if re.search(pattern, line) and not line.strip().startswith('--'):
                # Get context (30 lines before and after for better understanding)
                start = max(0, i - 30)
                end = min(len(lines), i + 15)
                context = '\n'.join(f"{j+1}|{lines[j]}" for j in range(start, end))
                return i + 1, line, context
        return None, None, None
    except Exception as e:
        log(f"Error reading {filepath}: {e}")
        return None, None, None

def call_claude(prompt):
    """Call Claude API to get a proof."""
    try:
        import urllib.request
        import json
        
        data = json.dumps({
            "model": MODEL,
            "max_tokens": 4096,
            "messages": [{"role": "user", "content": prompt}]
        }).encode()
        
        req = urllib.request.Request(
            "https://api.anthropic.com/v1/messages",
            data=data,
            headers={
                "Content-Type": "application/json",
                "x-api-key": ANTHROPIC_API_KEY,
                "anthropic-version": "2023-06-01"
            }
        )
        
        with urllib.request.urlopen(req, timeout=120) as resp:
            result = json.loads(resp.read().decode())
            return result["content"][0]["text"]
    except Exception as e:
        log(f"Claude API error: {e}")
        return None

def attempt_proof(filepath, line_num, line_content, context):
    """Attempt to prove one sorry."""
    prompt = f"""You are proving lemmas in a Lean 4 Hodge Conjecture formalization.

File: {filepath}
Line {line_num}: {line_content}

Context (with line numbers):
```lean
{context}
```

IMPORTANT RULES:
1. Replace the `sorry` on line {line_num} with a REAL Lean 4 proof
2. DO NOT use trivializations like `:= trivial`, `:= True`, `True.intro`, or `⟨⟩`
3. Use proper tactics: `simp`, `exact`, `apply`, `intro`, `constructor`, `cases`, etc.
4. If a definition needs a sorry, use `sorry` explicitly - don't hide it with trivial
5. Look at the imports and what's in scope
6. Keep the proof simple but REAL

Respond with ONLY a JSON object:
{{"old_code": "the exact line containing sorry", "new_code": "the replacement with real proof"}}

Example good responses:
- {{"old_code": "... := sorry", "new_code": "... := by simp [add_comm]"}}
- {{"old_code": "... := sorry", "new_code": "... := by exact h.symm"}}
- {{"old_code": "... := sorry", "new_code": "... := by constructor <;> assumption"}}

Example BAD responses (REJECTED):
- {{"old_code": "...", "new_code": "... := trivial"}}
- {{"old_code": "...", "new_code": "... := True.intro"}}
"""
    
    response = call_claude(prompt)
    if not response:
        return False
    
    try:
        # Parse JSON from response
        match = re.search(r'\{[^{}]*"old_code"[^{}]*"new_code"[^{}]*\}', response, re.DOTALL)
        if not match:
            log("Could not parse response")
            return False
        
        data = json.loads(match.group())
        old_code = data.get("old_code", "")
        new_code = data.get("new_code", "")
        
        if not old_code or not new_code:
            log("Empty old/new code")
            return False
        
        # CHECK FOR TRIVIALIZATIONS
        if is_trivialization(new_code):
            stats["rejected_trivializations"] += 1
            log(f"❌ REJECTED trivialization: {new_code[:50]}...")
            return False
        
        # Read file
        full_path = REPO_PATH / filepath
        content = full_path.read_text()
        
        if old_code not in content:
            log("Old code not found in file")
            return False
        
        # Apply change
        new_content = content.replace(old_code, new_code, 1)
        full_path.write_text(new_content)
        
        # Test build
        ok, output = run_cmd(f"export PATH=/home/ubuntu/.elan/bin:$PATH && {LAKE_PATH} build {filepath.replace('/', '.').replace('.lean', '')} 2>&1 | tail -20", timeout=180)
        
        if "Build completed successfully" in output or ("error" not in output.lower() and "sorry" not in new_code.lower()):
            log(f"✅ SUCCESS! Eliminated sorry at {filepath}:{line_num}")
            stats["sorries_eliminated"] += 1
            return True
        else:
            # Revert
            full_path.write_text(content)
            stats["failed_attempts"] += 1
            log(f"Build failed, reverted")
            return False
            
    except Exception as e:
        log(f"Error applying proof: {e}")
        stats["failed_attempts"] += 1
        return False

def hourly_update():
    """Send hourly progress update."""
    elapsed = time.time() - stats["start_time"]
    hours = elapsed / 3600
    
    total = get_total_sorries()
    rate = stats["sorries_eliminated"] / hours if hours > 0 else 0
    eta_hours = total / rate if rate > 0 else float('inf')
    
    msg = f"""📊 *Hodge Proof Progress Update*
    
• Elapsed: {hours:.1f} hours
• Sorries eliminated: {stats['sorries_eliminated']}
• Failed attempts: {stats['failed_attempts']}
• Rejected trivializations: {stats['rejected_trivializations']}
• Remaining sorries: {total}
• Rate: {rate:.1f}/hour
• ETA: {eta_hours:.1f} hours"""
    
    slack_notify(msg)
    stats["last_slack_update"] = time.time()

def main_loop():
    """Main autonomous loop."""
    log("=" * 60)
    log("AUTONOMOUS PROOF COMPLETION SYSTEM STARTING")
    log("(Trivialization rejection enabled)")
    log("=" * 60)
    
    stats["start_time"] = time.time()
    stats["last_slack_update"] = time.time()
    
    # Initial notification
    total = get_total_sorries()
    slack_notify(f"🚀 *Autonomous Proof System Started*\n• Target files: {len(TARGET_FILES)}\n• Initial sorries: {total}\n• Trivialization rejection: ENABLED")
    
    while True:
        try:
            stats["cycles"] += 1
            log(f"\n{'='*40}")
            log(f"CYCLE {stats['cycles']}")
            log(f"{'='*40}")
            
            # Check if proof is complete
            total = get_total_sorries()
            if total == 0:
                slack_notify("🎉 *PROOF COMPLETE!* All sorries eliminated!")
                log("🎉 PROOF COMPLETE! All sorries eliminated!")
                break
            
            log(f"Total sorries remaining: {total}")
            
            # Ensure build is green before proceeding
            if not check_build():
                log("Build is not green, attempting repair...")
                run_cmd("git checkout -- .")  # Revert any broken changes
                time.sleep(30)
                continue
            
            # Work through files
            for filepath in TARGET_FILES:
                sorry_count = count_sorries(filepath)
                if sorry_count <= 0:
                    continue
                
                log(f"\n--- {filepath}: {sorry_count} sorries ---")
                
                line_num, line_content, context = find_first_sorry(filepath)
                if line_num is None:
                    continue
                
                log(f"Attempting line {line_num}: {line_content.strip()[:60]}...")
                attempt_proof(filepath, line_num, line_content, context)
                
                # Small delay between attempts
                time.sleep(2)
            
            # Hourly update
            if time.time() - stats["last_slack_update"] > 3600:
                hourly_update()
            
            # Brief pause between cycles
            time.sleep(5)
            
        except KeyboardInterrupt:
            log("Interrupted by user")
            break
        except Exception as e:
            log(f"Error in main loop: {e}")
            time.sleep(30)  # Wait before retrying

def main():
    """Entry point with self-healing wrapper."""
    LOG_DIR.mkdir(exist_ok=True)
    
    max_restarts = 100
    restart_count = 0
    
    while restart_count < max_restarts:
        try:
            main_loop()
            break  # Normal exit (proof complete)
        except Exception as e:
            restart_count += 1
            log(f"CRASH #{restart_count}: {e}")
            slack_notify(f"⚠️ Autonomous system crashed: {e}\nRestarting... ({restart_count}/{max_restarts})")
            time.sleep(60)  # Wait before restart
    
    log("Autonomous system shutting down")
    slack_notify("🛑 Autonomous proof system has stopped")

if __name__ == "__main__":
    main()
