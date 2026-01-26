#!/usr/bin/env python3
"""
Parallel Prover Orchestrator

Runs multiple native_prover instances in parallel to work on different theorems.
Each prover works on one theorem with a tight compile-test-fix loop.
"""

import os
import sys
import json
import asyncio
import subprocess
from datetime import datetime

# Configuration
HODGE_DIR = "/home/ubuntu/hodge"
MAX_CONCURRENT = 4  # Number of parallel provers
STATE_FILE = "prover_state.json"

def find_sorries():
    """Find all sorry statements in the codebase and create tasks."""
    cmd = f"grep -rn 'sorry' {HODGE_DIR}/Hodge --include='*.lean' | grep -v '/\\.' | grep -v '.lake'"
    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)
    
    tasks = []
    for line in result.stdout.strip().split("\n"):
        if not line:
            continue
        if ":=" in line or "-- " in line:
            # Skip comments and definitions that mention sorry
            continue
        if "sorry" not in line.lower():
            continue
            
        parts = line.split(":", 2)
        if len(parts) < 3:
            continue
            
        filepath = parts[0].replace(HODGE_DIR + "/", "")
        line_num = int(parts[1])
        content = parts[2].strip()
        
        # Try to find the theorem name
        theorem_name = f"sorry_at_line_{line_num}"
        
        tasks.append({
            "file": filepath,
            "line": line_num,
            "name": theorem_name,
            "description": f"Eliminate sorry at line {line_num}",
            "content": content,
            "status": "pending"
        })
    
    return tasks

def load_state():
    """Load prover state from file."""
    state_path = os.path.join(HODGE_DIR, STATE_FILE)
    if os.path.exists(state_path):
        with open(state_path, 'r') as f:
            return json.load(f)
    return {"tasks": [], "completed": [], "failed": []}

def save_state(state):
    """Save prover state to file."""
    state_path = os.path.join(HODGE_DIR, STATE_FILE)
    with open(state_path, 'w') as f:
        json.dump(state, f, indent=2)

async def run_prover(task):
    """Run the native prover on a single task."""
    print(f"Starting prover for: {task['name']} in {task['file']}")
    
    task_json = json.dumps(task)
    cmd = f"cd {HODGE_DIR} && export PATH=$HOME/.elan/bin:$PATH && python3 scripts/agents/native_prover.py '{task_json}'"
    
    process = await asyncio.create_subprocess_shell(
        cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE
    )
    
    stdout, stderr = await process.communicate()
    
    return {
        "task": task,
        "returncode": process.returncode,
        "stdout": stdout.decode() if stdout else "",
        "stderr": stderr.decode() if stderr else ""
    }

async def run_parallel_provers(tasks):
    """Run multiple provers in parallel."""
    state = load_state()
    
    # Filter to pending tasks
    pending = [t for t in tasks if t["status"] == "pending"]
    
    if not pending:
        print("No pending tasks!")
        return
    
    print(f"Running {min(len(pending), MAX_CONCURRENT)} parallel provers...")
    
    # Run in batches
    while pending:
        batch = pending[:MAX_CONCURRENT]
        pending = pending[MAX_CONCURRENT:]
        
        print(f"\n{'='*60}")
        print(f"Starting batch of {len(batch)} provers")
        print(f"Remaining: {len(pending)}")
        print(f"{'='*60}\n")
        
        results = await asyncio.gather(*[run_prover(t) for t in batch])
        
        for result in results:
            task = result["task"]
            if result["returncode"] == 0 and "SUCCESS" in result["stdout"]:
                print(f"✅ {task['name']} - PROVED")
                state["completed"].append(task)
            else:
                print(f"❌ {task['name']} - FAILED")
                state["failed"].append(task)
            
            save_state(state)

def create_gmt_tasks():
    """Create tasks for the specific GMT theorems we need to prove."""
    return [
        {
            "file": "Hodge/Analytic/Currents.lean",
            "name": "stokes_bound",
            "description": "Prove Stokes' theorem bound: ∫_Z dω = ∫_∂Z ω",
            "context": """
Stokes' theorem for currents. The key is:
1. d is the exterior derivative
2. ∂Z is the boundary of Z
3. Integration of exact forms over closed submanifolds is zero

In Mathlib, look for:
- MeasureTheory.integral_eq_sum_of_hasFiniteIntegral
- Analysis.Calculus.Stokes
            """,
            "status": "pending"
        },
        {
            "file": "Hodge/Analytic/Integration/HausdorffMeasure.lean",
            "name": "hausdorffIntegrate_bound",
            "description": "Prove |∫_Z ω| ≤ mass(Z) · comass(ω)",
            "context": """
Mass-comass duality inequality. The proof uses:
1. |∫_Z ω| = |∫ ⟨ω, τ⟩ dμ| where τ is the orienting k-vector
2. By definition of comass: |⟨ω, τ⟩| ≤ comass(ω) when |τ| = 1
3. Triangle inequality: |∫ f dμ| ≤ ∫ |f| dμ
4. Therefore |∫_Z ω| ≤ comass(ω) · μ(Z) = comass(ω) · mass(Z)
            """,
            "status": "pending"
        },
        {
            "file": "Hodge/Classical/HarveyLawson.lean",
            "name": "flat_limit_is_integral",
            "description": "Prove flat limits of integral currents are integral",
            "context": """
This is Federer-Fleming compactness:
- If T_n are integral currents with uniformly bounded mass
- And T_n → T in the flat norm
- Then T is also an integral current

Key Mathlib concepts:
- Compactness in weak-* topology
- Rectifiable sets
- BV functions
            """,
            "status": "pending"
        },
        {
            "file": "Hodge/Analytic/Currents.lean", 
            "name": "integrate_linear",
            "description": "Prove integration is linear: ∫_Z (aω + bη) = a∫_Z ω + b∫_Z η",
            "context": """
Linearity of integration. This should follow from:
- Linearity of the integral in Mathlib
- Linearity of formVectorPairing
- Linearity of Complex.re
            """,
            "status": "pending"
        },
        {
            "file": "Hodge/Kahler/Microstructure.lean",
            "name": "is_integral_cycle",
            "description": "Prove the microstructure sequence consists of integral cycles",
            "context": """
The microstructure construction produces:
1. A sequence of currents T_n approaching the Hodge class
2. Each T_n is an integral current (integer multiplicities)
3. Each T_n is a cycle (∂T_n = 0)

For now the construction uses zero_int as a stub.
The real construction uses:
- Harvey-Lawson witness theorem
- Calibration theory
            """,
            "status": "pending"
        }
    ]

async def main():
    print("="*60)
    print("PARALLEL GMT PROVER")
    print("="*60)
    
    if "--scan" in sys.argv:
        print("\nScanning for sorry statements...")
        tasks = find_sorries()
        print(f"Found {len(tasks)} sorry statements")
        for t in tasks[:10]:
            print(f"  {t['file']}:{t['line']} - {t['content'][:50]}...")
    else:
        print("\nUsing predefined GMT tasks...")
        tasks = create_gmt_tasks()
        print(f"Created {len(tasks)} GMT proving tasks")
        for t in tasks:
            print(f"  {t['name']}: {t['description']}")
    
    await run_parallel_provers(tasks)
    
    state = load_state()
    print(f"\n{'='*60}")
    print("FINAL RESULTS")
    print(f"{'='*60}")
    print(f"Completed: {len(state.get('completed', []))}")
    print(f"Failed: {len(state.get('failed', []))}")

if __name__ == "__main__":
    asyncio.run(main())
