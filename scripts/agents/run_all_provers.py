#!/usr/bin/env python3
"""
Run all GMT prover tasks in parallel.
"""

import os
import sys
import json
import asyncio
import subprocess
from datetime import datetime

HODGE_DIR = "/home/ubuntu/hodge"
MAX_CONCURRENT = 4  # Run 4 provers at a time

async def run_prover(task, task_num, total):
    """Run native_prover on a single task."""
    print(f"[{task_num}/{total}] Starting: {task['name']}")
    
    log_file = f"prover_logs/{task['name']}_{datetime.now().strftime('%H%M%S')}.log"
    os.makedirs(os.path.join(HODGE_DIR, "prover_logs"), exist_ok=True)
    
    task_json = json.dumps(task).replace("'", "'\\''")  # Escape single quotes
    cmd = f"cd {HODGE_DIR} && export PATH=$HOME/.elan/bin:$PATH && python3 scripts/agents/native_prover.py '{task_json}' > {log_file} 2>&1"
    
    process = await asyncio.create_subprocess_shell(cmd)
    await process.wait()
    
    # Read log to check result
    log_path = os.path.join(HODGE_DIR, log_file)
    try:
        with open(log_path, 'r') as f:
            log_content = f.read()
        
        if "SUCCESS" in log_content:
            print(f"[{task_num}/{total}] ✅ {task['name']} - PROVED!")
            return {"task": task, "success": True, "log": log_file}
        else:
            print(f"[{task_num}/{total}] ❌ {task['name']} - Failed")
            return {"task": task, "success": False, "log": log_file}
    except:
        print(f"[{task_num}/{total}] ❓ {task['name']} - Unknown")
        return {"task": task, "success": False, "log": log_file}

async def main():
    # Load tasks
    tasks_file = os.path.join(HODGE_DIR, "scripts/agents/gmt_tasks.json")
    with open(tasks_file, 'r') as f:
        tasks = json.load(f)
    
    print(f"{'='*60}")
    print(f"GMT PARALLEL PROVER")
    print(f"{'='*60}")
    print(f"Tasks: {len(tasks)}")
    print(f"Concurrent: {MAX_CONCURRENT}")
    print(f"{'='*60}\n")
    
    # Create semaphore for concurrency control
    sem = asyncio.Semaphore(MAX_CONCURRENT)
    
    async def bounded_prover(task, num, total):
        async with sem:
            return await run_prover(task, num, total)
    
    # Run all tasks
    results = await asyncio.gather(
        *[bounded_prover(t, i+1, len(tasks)) for i, t in enumerate(tasks)]
    )
    
    # Summary
    successes = [r for r in results if r["success"]]
    failures = [r for r in results if not r["success"]]
    
    print(f"\n{'='*60}")
    print(f"FINAL RESULTS")
    print(f"{'='*60}")
    print(f"✅ Proved: {len(successes)}/{len(tasks)}")
    for r in successes:
        print(f"   - {r['task']['name']}")
    print(f"❌ Failed: {len(failures)}/{len(tasks)}")
    for r in failures:
        print(f"   - {r['task']['name']}")
    
    # Save results
    results_file = os.path.join(HODGE_DIR, f"prover_results_{datetime.now().strftime('%Y%m%d_%H%M%S')}.json")
    with open(results_file, 'w') as f:
        json.dump(results, f, indent=2, default=str)
    print(f"\nResults saved to: {results_file}")

if __name__ == "__main__":
    asyncio.run(main())
