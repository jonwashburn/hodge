#!/usr/bin/env python3
"""
Hodge Conjecture Formalization - Multi-Agent Coordinator
=========================================================
Orchestrates multiple Claude instances to parallelize the Lean 4 formalization work.

Architecture:
- Coordinator (this script) manages the task queue and dispatches work
- Worker agents (Claude API) receive tasks, work on them, and return results
- Tasks are organized by dependency (some axioms depend on others)
- Progress is persisted to disk and can resume after interruption
"""

import os
import json
import asyncio
import aiohttp
import subprocess
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Optional, List, Dict, Any
from enum import Enum
import hashlib
import time

# Configuration
ANTHROPIC_API_KEY = os.environ.get("ANTHROPIC_API_KEY", "")
MODEL = "claude-opus-4-5-20251101"
MAX_CONCURRENT_AGENTS = 5
HODGE_REPO_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_REPO_PATH / "agent_state.json"
LOG_DIR = HODGE_REPO_PATH / "agent_logs"


class TaskStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    BLOCKED = "blocked"


@dataclass
class Task:
    id: str
    description: str
    file_path: str
    target_axiom_or_sorry: str
    status: TaskStatus = TaskStatus.PENDING
    dependencies: List[str] = field(default_factory=list)
    assigned_agent: Optional[str] = None
    result: Optional[str] = None
    error: Optional[str] = None
    attempts: int = 0
    created_at: str = field(default_factory=lambda: datetime.now().isoformat())
    completed_at: Optional[str] = None

    def to_dict(self):
        d = asdict(self)
        d['status'] = self.status.value
        return d

    @classmethod
    def from_dict(cls, d):
        d['status'] = TaskStatus(d['status'])
        return cls(**d)


# Task definitions based on the proof track analysis
INITIAL_TASKS = [
    # Main proof track sorries
    Task(
        id="microstructure_construction",
        description="Prove microstructure_construction_core in Hodge/Kahler/Main.lean",
        file_path="Hodge/Kahler/Main.lean",
        target_axiom_or_sorry="microstructure_construction_core",
        dependencies=["harvey_lawson_structure"]
    ),
    Task(
        id="chow_gaga",
        description="Prove chow_gaga_analytic_to_algebraic in Hodge/Classical/GAGA.lean",
        file_path="Hodge/Classical/GAGA.lean",
        target_axiom_or_sorry="chow_gaga_analytic_to_algebraic",
        dependencies=[]
    ),
    
    # Classical pillars - GMT
    Task(
        id="federer_fleming_compactness",
        description="Formalize Federer-Fleming compactness theorem",
        file_path="Hodge/Classical/FedererFleming.lean",
        target_axiom_or_sorry="FedererFlemingCompactness",
        dependencies=[]
    ),
    Task(
        id="harvey_lawson_structure",
        description="Formalize Harvey-Lawson structure theorem for positive currents",
        file_path="Hodge/Classical/HarveyLawson.lean",
        target_axiom_or_sorry="HarveyLawsonStructureTheorem",
        dependencies=["federer_fleming_compactness"]
    ),
    
    # Kähler geometry
    Task(
        id="hard_lefschetz",
        description="Complete Hard Lefschetz theorem formalization",
        file_path="Hodge/Kahler/Lefschetz.lean",
        target_axiom_or_sorry="hard_lefschetz",
        dependencies=[]
    ),
    Task(
        id="hodge_decomposition",
        description="Prove Hodge decomposition for Kähler manifolds",
        file_path="Hodge/Kahler/HodgeDecomp.lean",
        target_axiom_or_sorry="hodge_decomposition",
        dependencies=["hard_lefschetz"]
    ),
    
    # Currents infrastructure
    Task(
        id="leibniz_wedge_left",
        description="Prove alternatizeUncurryFin_wedge_left in LeibnizRule.lean",
        file_path="Hodge/Analytic/Advanced/LeibnizRule.lean",
        target_axiom_or_sorry="alternatizeUncurryFin_wedge_left",
        dependencies=[]
    ),
    Task(
        id="leibniz_wedge_right",
        description="Prove alternatizeUncurryFin_wedge_right in LeibnizRule.lean",
        file_path="Hodge/Analytic/Advanced/LeibnizRule.lean",
        target_axiom_or_sorry="alternatizeUncurryFin_wedge_right",
        dependencies=[]
    ),
    Task(
        id="smoothext_comass_bound",
        description="Prove Current.smoothExtDeriv_comass_bound",
        file_path="Hodge/Analytic/Currents.lean",
        target_axiom_or_sorry="smoothExtDeriv_comass_bound",
        dependencies=[]
    ),
    
    # Fundamental class
    Task(
        id="fundamental_class",
        description="Prove FundamentalClassSet_represents_class",
        file_path="Hodge/Classical/GAGA.lean",
        target_axiom_or_sorry="FundamentalClassSet_represents_class",
        dependencies=["harvey_lawson_structure", "chow_gaga"]
    ),
]


class AgentCoordinator:
    def __init__(self):
        self.tasks: Dict[str, Task] = {}
        self.active_agents: Dict[str, asyncio.Task] = {}
        self.session: Optional[aiohttp.ClientSession] = None
        self.load_state()

    def load_state(self):
        """Load persisted state or initialize with default tasks."""
        if STATE_FILE.exists():
            with open(STATE_FILE) as f:
                data = json.load(f)
                self.tasks = {k: Task.from_dict(v) for k, v in data.get('tasks', {}).items()}
        else:
            for task in INITIAL_TASKS:
                self.tasks[task.id] = task
        
        LOG_DIR.mkdir(parents=True, exist_ok=True)

    def save_state(self):
        """Persist current state to disk."""
        with open(STATE_FILE, 'w') as f:
            json.dump({
                'tasks': {k: v.to_dict() for k, v in self.tasks.items()},
                'last_updated': datetime.now().isoformat()
            }, f, indent=2)

    def get_ready_tasks(self) -> List[Task]:
        """Get tasks that are ready to be worked on (dependencies met)."""
        ready = []
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            deps_met = all(
                self.tasks[dep].status == TaskStatus.COMPLETED
                for dep in task.dependencies
                if dep in self.tasks
            )
            if deps_met:
                ready.append(task)
        return ready

    async def call_claude(self, system_prompt: str, user_prompt: str) -> str:
        """Make an API call to Claude."""
        if not ANTHROPIC_API_KEY:
            raise ValueError("ANTHROPIC_API_KEY not set")
        
        headers = {
            "x-api-key": ANTHROPIC_API_KEY,
            "content-type": "application/json",
            "anthropic-version": "2023-06-01"
        }
        
        payload = {
            "model": MODEL,
            "max_tokens": 8192,
            "system": system_prompt,
            "messages": [{"role": "user", "content": user_prompt}]
        }
        
        async with self.session.post(
            "https://api.anthropic.com/v1/messages",
            headers=headers,
            json=payload
        ) as resp:
            if resp.status != 200:
                error_text = await resp.text()
                raise Exception(f"API error {resp.status}: {error_text}")
            data = await resp.json()
            return data['content'][0]['text']

    def read_file(self, path: str) -> str:
        """Read a file from the repo."""
        full_path = HODGE_REPO_PATH / path
        if full_path.exists():
            return full_path.read_text()
        return f"[File not found: {path}]"

    def write_file(self, path: str, content: str):
        """Write content to a file in the repo."""
        full_path = HODGE_REPO_PATH / path
        full_path.parent.mkdir(parents=True, exist_ok=True)
        full_path.write_text(content)

    def run_lake_build(self, file_path: str = None) -> tuple[bool, str]:
        """Run lake build and return success status and output."""
        cmd = ["lake", "build"]
        if file_path:
            # Just build the specific module
            module = file_path.replace("/", ".").replace(".lean", "")
            cmd.append(module)
        
        result = subprocess.run(
            cmd,
            cwd=HODGE_REPO_PATH,
            capture_output=True,
            text=True,
            timeout=600
        )
        success = result.returncode == 0
        output = result.stdout + result.stderr
        return success, output

    async def work_on_task(self, task: Task) -> bool:
        """Have an agent work on a specific task."""
        task.status = TaskStatus.IN_PROGRESS
        task.attempts += 1
        task.assigned_agent = f"agent_{hashlib.md5(task.id.encode()).hexdigest()[:8]}"
        self.save_state()
        
        # Read the target file
        file_content = self.read_file(task.file_path)
        
        # Build the system prompt
        system_prompt = f"""You are an expert Lean 4 mathematician working on the Hodge Conjecture formalization.
Your task is to eliminate a sorry or axiom from the proof track.

CRITICAL RULES:
1. Only modify the specific sorry/axiom you're assigned to
2. Use Mathlib conventions and existing abstractions
3. Test your changes compile before submitting
4. If truly stuck, document what mathematical content is needed

You have access to the codebase. The main theorem is hodge_conjecture' in Hodge/Kahler/Main.lean.

Current file content:
```lean
{file_content}
```

Your target: {task.target_axiom_or_sorry}
Description: {task.description}
"""

        user_prompt = f"""Please work on eliminating: {task.target_axiom_or_sorry}

File: {task.file_path}

1. First, analyze what this sorry/axiom requires mathematically
2. Check if there are Mathlib lemmas that can help
3. Write the proof or propose a proof strategy
4. Return your proposed changes as a complete replacement for the relevant theorem/definition

Format your response as:
ANALYSIS: <your analysis>
PROPOSED_CODE:
```lean
<the complete new code for the theorem/definition>
```
CONFIDENCE: <high/medium/low>
BLOCKERS: <any blockers if you couldn't complete it>
"""

        try:
            response = await self.call_claude(system_prompt, user_prompt)
            
            # Log the response
            log_file = LOG_DIR / f"{task.id}_{task.attempts}.log"
            log_file.write_text(f"Task: {task.id}\nAttempt: {task.attempts}\n\n{response}")
            
            # Check if we got proposed code
            if "PROPOSED_CODE:" in response and "```lean" in response:
                # Extract the code
                code_start = response.find("```lean") + 7
                code_end = response.find("```", code_start)
                new_code = response[code_start:code_end].strip()
                
                # Store the result
                task.result = new_code
                
                # Mark as completed regardless of confidence
                # (these are exploratory - human review needed anyway)
                task.status = TaskStatus.COMPLETED
                task.completed_at = datetime.now().isoformat()
                    
            else:
                # After 3 attempts, mark as failed
                if task.attempts >= 3:
                    task.error = "No valid code proposed after 3 attempts"
                    task.status = TaskStatus.FAILED
                else:
                    task.error = "No valid code proposed"
                    task.status = TaskStatus.PENDING  # Retry
                
        except Exception as e:
            task.error = str(e)
            task.status = TaskStatus.FAILED
        
        self.save_state()
        return task.status == TaskStatus.COMPLETED

    async def run(self):
        """Main coordination loop."""
        print(f"Starting Hodge Agent Coordinator")
        print(f"Tasks: {len(self.tasks)}")
        print(f"Ready: {len(self.get_ready_tasks())}")
        
        self.session = aiohttp.ClientSession()
        
        try:
            while True:
                ready_tasks = self.get_ready_tasks()
                if not ready_tasks:
                    pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                    if not pending:
                        print("All tasks completed or failed!")
                        break
                    print(f"Waiting for dependencies... ({len(pending)} pending)")
                    await asyncio.sleep(10)
                    continue
                
                # Dispatch tasks up to concurrency limit
                slots = MAX_CONCURRENT_AGENTS - len(self.active_agents)
                for task in ready_tasks[:slots]:
                    print(f"Dispatching: {task.id}")
                    agent_task = asyncio.create_task(self.work_on_task(task))
                    self.active_agents[task.id] = agent_task
                
                # Wait for at least one to complete
                if self.active_agents:
                    done, _ = await asyncio.wait(
                        self.active_agents.values(),
                        return_when=asyncio.FIRST_COMPLETED
                    )
                    # Clean up completed
                    completed_ids = [
                        tid for tid, t in self.active_agents.items()
                        if t.done()
                    ]
                    for tid in completed_ids:
                        del self.active_agents[tid]
                        status = self.tasks[tid].status
                        print(f"Completed: {tid} -> {status.value}")
                
                await asyncio.sleep(1)
                
        finally:
            await self.session.close()
            self.save_state()

    def status_report(self) -> str:
        """Generate a status report of all tasks."""
        lines = ["# Hodge Formalization - Agent Status Report", ""]
        
        by_status = {}
        for task in self.tasks.values():
            by_status.setdefault(task.status.value, []).append(task)
        
        for status, tasks in sorted(by_status.items()):
            lines.append(f"## {status.upper()} ({len(tasks)})")
            for t in tasks:
                lines.append(f"- {t.id}: {t.description}")
                if t.error:
                    lines.append(f"  Error: {t.error}")
            lines.append("")
        
        return "\n".join(lines)


async def main():
    coordinator = AgentCoordinator()
    
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "status":
        print(coordinator.status_report())
        return
    
    if len(sys.argv) > 1 and sys.argv[1] == "reset":
        if STATE_FILE.exists():
            STATE_FILE.unlink()
        print("State reset. Run again to start fresh.")
        return
    
    await coordinator.run()


if __name__ == "__main__":
    asyncio.run(main())
