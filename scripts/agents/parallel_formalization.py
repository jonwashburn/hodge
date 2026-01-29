#!/usr/bin/env python3
"""
Parallel Formalization Coordinator
===================================
Manages parallel agents working on the full Hodge Conjecture formalization
according to the stage-based plan.

Tracks:
- Track A: GMT/Currents (Stages 1→2→3→4) - Sequential
- Track B: Algebraic Geometry (Stage 5) - Parallel to A
- Track C: Cohomology (Stage 6) - After A+B complete
"""

import os
import json
import asyncio
import aiohttp
import re
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional, List, Dict
from enum import Enum

# Configuration
API_KEY = ""
for p in [Path.home() / ".anthropic_api_key", Path.home() / ".anthropic_key"]:
    try:
        if p.exists():
            API_KEY = p.read_text().strip()
            break
    except:
        pass

MODEL = "claude-opus-4-5-20251101"
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "parallel_state.json"
LOG_DIR = HODGE_PATH / "parallel_logs"
PAPER_PATH = HODGE_PATH / "JA_hodge_approach_with_added_refs_blueCites.tex"

# Track definitions
TRACK_A_STAGES = [1, 2, 3, 4]  # Sequential
TRACK_B_STAGES = [5]           # Parallel to A
TRACK_C_STAGES = [6, 7]        # After A+B

# File assignments by stage
STAGE_FILES = {
    1: [
        "Hodge/Analytic/TestForms/LFTopology.lean",
        "Hodge/Analytic/TestForms/Operations.lean",
        "Hodge/Analytic/TestForms/CurrentsDual.lean",
    ],
    2: [
        "Hodge/Analytic/Integration/SubmanifoldIntegral.lean",
        "Hodge/Analytic/Integration/IntegrationCurrent.lean",
        "Hodge/Analytic/Integration/Stokes.lean",
    ],
    3: [
        "Hodge/GMT/Mass.lean",
        "Hodge/GMT/FlatNorm.lean",
    ],
    4: [
        "Hodge/GMT/Calibration.lean",
    ],
    5: [
        "Hodge/AlgGeom/AnalyticSetsReal.lean",
        "Hodge/AlgGeom/GAGAReal.lean",
    ],
    6: [
        "Hodge/Cohomology/CohomologyReal.lean",
    ],
    7: [
        "Hodge/Kahler/Main.lean",  # Final wiring - fix the 2 sorries
    ],
}

VISION = """
## THE HODGE CONJECTURE FORMALIZATION

You are working on a formal proof of the Hodge Conjecture in Lean 4.
This is a Millennium Prize Problem.

### The Proof Strategy
1. Rational Hodge class → Microstructure with vanishing calibration defect
2. Calibrated currents → Analytic variety support (Harvey-Lawson)
3. Analytic varieties → Algebraic (Chow/GAGA)
4. Therefore: Rational Hodge classes are algebraic

### Your Task
Complete the Lean 4 implementation in the assigned file.
Use Mathlib infrastructure where possible.
Replace `sorry` with real proofs.
Use `sorryAx` only for genuinely deep results.
"""

class TaskStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"

@dataclass
class FileTask:
    file_path: str
    stage: int
    track: str
    status: TaskStatus = TaskStatus.PENDING
    attempts: int = 0
    sorries_remaining: int = -1
    
    def to_dict(self):
        return {
            "file_path": self.file_path,
            "stage": self.stage,
            "track": self.track,
            "status": self.status.value,
            "attempts": self.attempts,
            "sorries_remaining": self.sorries_remaining
        }
    
    @classmethod
    def from_dict(cls, d):
        d["status"] = TaskStatus(d["status"])
        return cls(**d)


class ParallelCoordinator:
    def __init__(self):
        self.tasks: Dict[str, FileTask] = {}
        self.semaphore = asyncio.Semaphore(15)  # Max parallel agents
        self.worker_count = 0
        LOG_DIR.mkdir(exist_ok=True)
        
    def load_state(self):
        if STATE_FILE.exists():
            try:
                data = json.loads(STATE_FILE.read_text())
                for t in data.get("tasks", []):
                    task = FileTask.from_dict(t)
                    self.tasks[task.file_path] = task
                print(f"Loaded {len(self.tasks)} tasks")
                return
            except Exception as e:
                print(f"Load error: {e}")
        
        # Initialize from stage files
        for stage, files in STAGE_FILES.items():
            track = "A" if stage in TRACK_A_STAGES else "B" if stage in TRACK_B_STAGES else "C"
            for f in files:
                self.tasks[f] = FileTask(file_path=f, stage=stage, track=track)
        print(f"Initialized {len(self.tasks)} tasks")
    
    def save_state(self):
        STATE_FILE.write_text(json.dumps({
            "tasks": [t.to_dict() for t in self.tasks.values()],
            "updated": datetime.now().isoformat()
        }, indent=2))
    
    def get_ready_tasks(self) -> List[FileTask]:
        """Get tasks that can run now based on dependencies."""
        ready = []
        
        # Track A is sequential
        track_a_completed = {s for s in TRACK_A_STAGES 
                           if all(self.tasks[f].status == TaskStatus.COMPLETED 
                                 for f in STAGE_FILES.get(s, []))}
        
        # Track B can run in parallel after stage 0
        # Track C needs both A and B complete
        
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            
            # Check stage dependencies
            if task.track == "A":
                # Track A: previous stage must be complete
                prev_stage = task.stage - 1
                if prev_stage > 0 and prev_stage not in track_a_completed:
                    continue
            elif task.track == "B":
                # Track B: can start immediately
                pass
            elif task.track == "C":
                # Track C: needs stages 4 and 5 complete
                if 4 not in track_a_completed:
                    continue
                stage5_done = all(self.tasks[f].status == TaskStatus.COMPLETED 
                                 for f in STAGE_FILES.get(5, []))
                if not stage5_done:
                    continue
            
            ready.append(task)
        
        return sorted(ready, key=lambda t: (t.stage, t.file_path))
    
    async def work_on_file(self, task: FileTask) -> bool:
        """Agent works on a single file."""
        worker_id = f"worker_{self.worker_count}"
        self.worker_count += 1
        log_file = LOG_DIR / f"{worker_id}.log"
        
        def log(msg):
            line = f"[{datetime.now():%H:%M:%S}] {msg}\n"
            with open(log_file, "a") as f:
                f.write(line)
            print(f"[{worker_id}] {msg}")
        
        log(f"Starting: {task.file_path} (Stage {task.stage})")
        task.status = TaskStatus.IN_PROGRESS
        task.attempts += 1
        self.save_state()
        
        file_path = HODGE_PATH / task.file_path
        if not file_path.exists():
            log(f"File not found: {task.file_path}")
            task.status = TaskStatus.FAILED
            return False
        
        content = file_path.read_text()
        sorry_count = content.count("sorry")
        log(f"File has {sorry_count} sorries to eliminate")
        
        prompt = f"""{VISION}

## YOUR FILE: {task.file_path}
## STAGE: {task.stage}
## TRACK: {task.track}

Current content:
```lean
{content[:8000]}
```

{f"(truncated, {len(content)} chars total)" if len(content) > 8000 else ""}

## INSTRUCTIONS

1. Read the file carefully - understand its mathematical purpose
2. Implement the `sorry` statements with real proofs
3. Use Mathlib lemmas where available
4. For deep results, use `sorryAx "description"` with clear comments

Output the COMPLETE updated file (or key sections with your changes).
Say "TASK_COMPLETE" when you have a working implementation.
"""
        
        messages = [{"role": "user", "content": prompt}]
        
        async with self.semaphore:
            for iteration in range(8):
                log(f"Iteration {iteration + 1}")
                
                response = await self._call_api(messages)
                if not response:
                    await asyncio.sleep(2)
                    continue
                
                messages.append({"role": "assistant", "content": response})
                
                # Extract code
                code_match = re.search(r"```lean\n(.*?)```", response, re.DOTALL)
                if code_match:
                    new_code = code_match.group(1)
                    if len(new_code) > 500:  # Substantial content
                        file_path.write_text(new_code)
                        log(f"Wrote {len(new_code)} chars")
                        
                        # Check build
                        ok, output = await self._build()
                        if ok:
                            log("BUILD SUCCESS!")
                            task.status = TaskStatus.COMPLETED
                            task.sorries_remaining = new_code.count("sorry")
                            self.save_state()
                            return True
                        else:
                            log("Build failed, iterating...")
                            file_path.write_text(content)  # Restore
                            messages.append({
                                "role": "user",
                                "content": f"Build failed:\n```\n{output[:2000]}\n```\nFix the errors."
                            })
                
                if "TASK_COMPLETE" in response and "sorry" not in response.lower():
                    log("Claimed complete but need to verify build")
                
                await asyncio.sleep(0.5)
        
        log("Max iterations reached")
        task.status = TaskStatus.PENDING  # Can retry
        self.save_state()
        return False
    
    async def _call_api(self, messages):
        if not API_KEY:
            return None
        async with aiohttp.ClientSession() as session:
            try:
                async with session.post(
                    "https://api.anthropic.com/v1/messages",
                    headers={
                        "x-api-key": API_KEY,
                        "anthropic-version": "2023-06-01",
                        "content-type": "application/json"
                    },
                    json={"model": MODEL, "max_tokens": 8192, "messages": messages},
                    timeout=aiohttp.ClientTimeout(total=300)
                ) as resp:
                    if resp.status != 200:
                        return None
                    data = await resp.json()
                    return data.get("content", [{}])[0].get("text", "")
            except:
                return None
    
    async def _build(self):
        try:
            proc = await asyncio.create_subprocess_exec(
                "lake", "build",
                cwd=str(HODGE_PATH),
                stdout=asyncio.subprocess.PIPE,
                stderr=asyncio.subprocess.PIPE
            )
            stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=600)
            return proc.returncode == 0, (stdout + stderr).decode()
        except Exception as e:
            return False, str(e)
    
    async def run(self):
        print("=" * 60)
        print("PARALLEL HODGE FORMALIZATION")
        print("Tracks: A (GMT) | B (AlgGeom) | C (Cohomology)")
        print("=" * 60)
        
        if not API_KEY:
            print("ERROR: No API key")
            return
        
        self.load_state()
        active: List[asyncio.Task] = []
        
        while True:
            active = [t for t in active if not t.done()]
            ready = self.get_ready_tasks()
            
            if not ready and not active:
                pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                if not pending:
                    print("\n" + "=" * 60)
                    print("ALL STAGES COMPLETE!")
                    print("=" * 60)
                    break
                await asyncio.sleep(5)
                continue
            
            # Launch workers
            for task in ready[:15 - len(active)]:
                print(f"Launching: Stage {task.stage} - {task.file_path}")
                active.append(asyncio.create_task(self.work_on_file(task)))
            
            # Status
            completed = sum(1 for t in self.tasks.values() if t.status == TaskStatus.COMPLETED)
            print(f"Progress: {completed}/{len(self.tasks)} | Active: {len(active)}")
            
            await asyncio.sleep(3)


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "status":
        if STATE_FILE.exists():
            data = json.loads(STATE_FILE.read_text())
            for t in data.get("tasks", []):
                print(f"Stage {t['stage']} | {t['status']:12} | {t['file_path']}")
    else:
        asyncio.run(ParallelCoordinator().run())
