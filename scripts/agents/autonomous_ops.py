#!/usr/bin/env python3
"""
Autonomous Ops Agent for Hodge Conjecture Formalization
========================================================
Fully autonomous system that completes the proof without human intervention.

Architecture:
- Master Orchestrator: Plans tasks, monitors progress, consults paper
- Worker Swarm: 20+ parallel agents doing actual Lean work  
- Reference Engine: Parses mathematical paper for guidance
- Self-Healing: Retries with escalating strategies

This runs indefinitely until the proof is complete.
"""

import os
import json
import asyncio
import aiohttp
import subprocess
import re
from dataclasses import dataclass, field, asdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional, List, Dict, Any, Tuple
from enum import Enum
import traceback
import hashlib


# =============================================================================
# Configuration
# =============================================================================

def _load_api_key():
    key = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if key:
        return key
    for p in [Path.home() / ".anthropic_api_key", Path.home() / ".anthropic_key"]:
        try:
            if p.exists():
                return p.read_text().strip()
        except:
            pass
    return ""

API_KEY = _load_api_key()
MODEL = "claude-opus-4-5-20251101"
OPUS_MODEL = "claude-opus-4-5-20251101"  # For hard problems
MAX_WORKERS = 20
MAX_TASK_ATTEMPTS = 5
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "autonomous_state.json"
LOG_DIR = HODGE_PATH / "autonomous_logs"
PAPER_PATH = HODGE_PATH / "JA_hodge_approach_with_added_refs_blueCites.tex"

# =============================================================================
# Data Structures
# =============================================================================

class TaskStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"
    BLOCKED = "blocked"

class TaskPriority(int, Enum):
    CRITICAL = 0  # Blocking other tasks
    HIGH = 1      # On critical path
    MEDIUM = 2    # Important
    LOW = 3       # Nice to have

@dataclass
class Task:
    id: str
    description: str
    file_path: str
    target: str
    status: TaskStatus = TaskStatus.PENDING
    priority: TaskPriority = TaskPriority.MEDIUM
    dependencies: List[str] = field(default_factory=list)
    attempts: int = 0
    last_error: Optional[str] = None
    assigned_worker: Optional[str] = None
    paper_sections: List[str] = field(default_factory=list)  # Relevant paper sections
    
    def to_dict(self):
        d = asdict(self)
        d["status"] = self.status.value
        d["priority"] = self.priority.value
        return d
    
    @classmethod
    def from_dict(cls, d):
        d["status"] = TaskStatus(d["status"])
        d["priority"] = TaskPriority(d["priority"]) if "priority" in d else TaskPriority.MEDIUM
        return cls(**d)

# =============================================================================
# Paper Reference Engine
# =============================================================================

class PaperReferenceEngine:
    """Parses and indexes the mathematical paper for reference."""
    
    def __init__(self, paper_path: Path):
        self.paper_path = paper_path
        self.sections: Dict[str, str] = {}
        self.theorems: Dict[str, str] = {}
        self.definitions: Dict[str, str] = {}
        self.full_text = ""
        self._parse()
    
    def _parse(self):
        if not self.paper_path.exists():
            print(f"Warning: Paper not found at {self.paper_path}")
            return
        
        self.full_text = self.paper_path.read_text(errors="ignore")
        
        # Extract sections
        section_pattern = r"\\section\{([^}]+)\}(.*?)(?=\\section|\\end\{document\}|$)"
        for match in re.finditer(section_pattern, self.full_text, re.DOTALL):
            title = match.group(1).strip()
            content = match.group(2).strip()
            self.sections[title] = content
        
        # Extract theorems
        thm_pattern = r"\\begin\{(theorem|proposition|lemma)\}(?:\[([^\]]+)\])?(.*?)\\end\{\1\}"
        for match in re.finditer(thm_pattern, self.full_text, re.DOTALL):
            thm_type = match.group(1)
            label = match.group(2) or f"{thm_type}_{len(self.theorems)}"
            content = match.group(3).strip()
            self.theorems[label] = f"[{thm_type}] {content}"
        
        # Extract definitions
        def_pattern = r"\\begin\{definition\}(?:\[([^\]]+)\])?(.*?)\\end\{definition\}"
        for match in re.finditer(def_pattern, self.full_text, re.DOTALL):
            label = match.group(1) or f"def_{len(self.definitions)}"
            content = match.group(2).strip()
            self.definitions[label] = content
        
        print(f"Paper indexed: {len(self.sections)} sections, {len(self.theorems)} theorems, {len(self.definitions)} definitions")
    
    def get_relevant_context(self, query: str, max_chars: int = 8000) -> str:
        """Get paper content relevant to a query."""
        query_lower = query.lower()
        relevant = []
        
        # Check section titles
        for title, content in self.sections.items():
            if any(word in title.lower() for word in query_lower.split()):
                relevant.append(f"=== Section: {title} ===\n{content[:2000]}")
        
        # Check theorems
        for label, content in self.theorems.items():
            if any(word in content.lower() for word in query_lower.split()):
                relevant.append(f"=== {label} ===\n{content}")
        
        # Check definitions
        for label, content in self.definitions.items():
            if any(word in content.lower() for word in query_lower.split()):
                relevant.append(f"=== Definition: {label} ===\n{content}")
        
        result = "\n\n".join(relevant)
        return result[:max_chars] if result else self.full_text[:max_chars]
    
    def get_proof_strategy(self, target: str) -> str:
        """Get proof strategy hints from the paper."""
        # Keywords to look for
        keywords = {
            "calibrat": ["calibration", "calibrated", "Harvey-Lawson"],
            "current": ["currents", "boundary", "integration"],
            "cycle": ["algebraic cycle", "Hodge class", "rational"],
            "cohomology": ["de Rham", "Dolbeault", "Poincare"],
            "GAGA": ["Chow", "algebraic", "analytic"],
            "microstructure": ["approximation", "sequence", "limit"],
        }
        
        for key, terms in keywords.items():
            if key in target.lower():
                return self.get_relevant_context(" ".join(terms))
        
        return self.get_relevant_context(target)

# =============================================================================
# Build & Validation
# =============================================================================

async def run_lake_build(file_path: str = None) -> Tuple[bool, str]:
    """Run lake build and return (success, output)."""
    try:
        # Cache first
        proc = await asyncio.create_subprocess_exec(
            "lake", "exe", "cache", "get",
            cwd=str(HODGE_PATH),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        await asyncio.wait_for(proc.communicate(), timeout=300)
        
        # Build
        cmd = ["lake", "build"]
        if file_path:
            module = file_path.replace("/", ".").replace(".lean", "")
            cmd.append(module)
        
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            cwd=str(HODGE_PATH),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=600)
        output = (stdout + stderr).decode()
        return proc.returncode == 0, output
    except asyncio.TimeoutError:
        return False, "Build timed out"
    except Exception as e:
        return False, str(e)

async def check_axioms() -> Tuple[bool, str]:
    """Check what axioms the proof depends on."""
    try:
        proc = await asyncio.create_subprocess_exec(
            "lake", "env", "lean", "Hodge/Utils/DependencyCheck.lean",
            cwd=str(HODGE_PATH),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=300)
        output = (stdout + stderr).decode()
        
        # Check for only standard axioms
        if "sorryAx" not in output and "axiom" not in output.lower():
            return True, "Clean - only standard axioms"
        return False, output
    except Exception as e:
        return False, str(e)

# =============================================================================
# Task Discovery
# =============================================================================

def discover_tasks() -> List[Task]:
    """Dynamically discover tasks from the codebase."""
    tasks = []
    
    # Scan for sorry/sorryAx in the proof track
    proof_track_files = [
        "Hodge/Kahler/Main.lean",
        "Hodge/Analytic/Forms.lean",
        "Hodge/Analytic/Currents.lean",
        "Hodge/Classical/HarveyLawsonReal.lean",
        "Hodge/Classical/GeometricCycleClass.lean",
    ]
    
    for file_rel in proof_track_files:
        file_path = HODGE_PATH / file_rel
        if not file_path.exists():
            continue
        
        content = file_path.read_text()
        
        # Find sorry statements
        for i, line in enumerate(content.split("\n")):
            if "sorry" in line.lower() and not line.strip().startswith("--"):
                # Extract context
                start = max(0, i - 5)
                end = min(len(content.split("\n")), i + 5)
                context = "\n".join(content.split("\n")[start:end])
                
                # Try to find the theorem/def name
                name_match = re.search(r"(theorem|lemma|def|instance)\s+(\w+)", context)
                name = name_match.group(2) if name_match else f"sorry_line_{i}"
                
                tasks.append(Task(
                    id=f"{file_rel}:{name}",
                    description=f"Prove {name} in {file_rel}",
                    file_path=file_rel,
                    target=name,
                    priority=TaskPriority.HIGH if "Main.lean" in file_rel else TaskPriority.MEDIUM
                ))
    
    # Add Stage 1-7 scaffolding tasks
    stage_tasks = [
        ("stage1_test_forms", "Hodge/Analytic/Stage1/TestForms.lean", "Complete LF-space test forms"),
        ("stage1_d_clm", "Hodge/Analytic/Stage1/EuclidTestFormsDeriv.lean", "Prove dCLM continuity"),
        ("stage2_integration", "Hodge/Analytic/Stage2/IntegrationCurrentsReal.lean", "Real integration currents"),
        ("stage3_mass", "Hodge/Analytic/MassReal.lean", "Proper mass definition"),
        ("stage3_flat_norm", "Hodge/Analytic/FlatNormReal.lean", "Flat norm definition"),
        ("stage4_calibration", "Hodge/Analytic/CalibrationReal.lean", "Calibration theory"),
        ("stage5_analytic_sets", "Hodge/AlgGeom/AnalyticSetsReal.lean", "Analytic sets via zero sets"),
        ("stage5_gaga", "Hodge/AlgGeom/GAGAReal.lean", "GAGA theorem"),
        ("stage6_cohomology", "Hodge/Cohomology/CohomologyReal.lean", "Cohomology bridge"),
    ]
    
    for task_id, file_path, desc in stage_tasks:
        if not (HODGE_PATH / file_path).exists():
            tasks.append(Task(
                id=task_id,
                description=desc,
                file_path=file_path,
                target="create_file",
                priority=TaskPriority.HIGH
            ))
    
    return tasks

# =============================================================================
# Worker Agent
# =============================================================================

class WorkerAgent:
    """Individual worker that executes tasks."""
    
    def __init__(self, worker_id: str, paper: PaperReferenceEngine):
        self.worker_id = worker_id
        self.paper = paper
        self.log_file = LOG_DIR / f"{worker_id}.log"
    
    def log(self, msg: str):
        timestamp = datetime.now().strftime("%H:%M:%S")
        line = f"[{timestamp}] {msg}\n"
        with open(self.log_file, "a") as f:
            f.write(line)
        print(f"[{self.worker_id}] {msg}")
    
    async def execute(self, task: Task) -> bool:
        """Execute a task with escalating strategies."""
        self.log(f"Starting task: {task.description}")
        
        # Get paper context
        paper_context = self.paper.get_proof_strategy(task.target)
        
        # Strategy 1: Direct implementation
        if await self._try_direct(task, paper_context):
            return True
        
        # Strategy 2: With more paper context
        if task.attempts < 2:
            full_context = self.paper.get_relevant_context(task.description, max_chars=15000)
            if await self._try_with_guidance(task, full_context):
                return True
        
        # Strategy 3: Use Opus for hard problems
        if task.attempts < 4:
            if await self._try_with_opus(task, paper_context):
                return True
        
        self.log(f"Task failed after {task.attempts} attempts")
        return False
    
    async def _try_direct(self, task: Task, paper_context: str) -> bool:
        """Try direct implementation."""
        prompt = self._build_prompt(task, paper_context, strategy="direct")
        return await self._run_loop(task, prompt, MODEL)
    
    async def _try_with_guidance(self, task: Task, paper_context: str) -> bool:
        """Try with detailed paper guidance."""
        prompt = self._build_prompt(task, paper_context, strategy="guided")
        return await self._run_loop(task, prompt, MODEL)
    
    async def _try_with_opus(self, task: Task, paper_context: str) -> bool:
        """Use Opus for hard problems."""
        self.log("Escalating to Opus model")
        prompt = self._build_prompt(task, paper_context, strategy="opus")
        return await self._run_loop(task, prompt, OPUS_MODEL)
    
    def _build_prompt(self, task: Task, paper_context: str, strategy: str) -> str:
        base = f"""You are an expert Lean 4 / Mathlib developer formalizing the Hodge Conjecture.

TASK: {task.description}
FILE: {task.file_path}
TARGET: {task.target}

MATHEMATICAL REFERENCE (from the proof paper):
{paper_context}

"""
        if strategy == "direct":
            return base + """Implement this directly. Use Mathlib lemmas where possible.
The code must compile with `lake build`. Say TASK_COMPLETE when done."""
        
        elif strategy == "guided":
            return base + """The previous attempt failed. Study the paper reference carefully and:
1. Understand the mathematical structure
2. Find the corresponding Mathlib concepts
3. Implement step by step

Be thorough. Say TASK_COMPLETE when done."""
        
        else:  # opus
            return base + """This is a HARD problem that has failed multiple attempts.

Take your time. Think deeply about:
1. What the mathematics really means
2. How to translate it to type theory
3. What Mathlib infrastructure exists

If a real proof is too complex, you may use `sorryAx` with a clear comment
explaining what deep mathematics is being assumed.

Say TASK_COMPLETE when done."""
    
    async def _run_loop(self, task: Task, initial_prompt: str, model: str) -> bool:
        """Run the agent loop."""
        messages = [{"role": "user", "content": initial_prompt}]
        
        for iteration in range(10):
            self.log(f"Iteration {iteration + 1}")
            
            response = await self._call_claude(messages, model)
            if not response:
                await asyncio.sleep(2)
                continue
            
            messages.append({"role": "assistant", "content": response})
            
            # Apply any code changes
            if "```lean" in response:
                await self._apply_code(task, response)
            
            # Check completion
            if "TASK_COMPLETE" in response:
                ok, output = await run_lake_build(task.file_path)
                if ok:
                    self.log("Build successful!")
                    return True
                else:
                    messages.append({
                        "role": "user",
                        "content": f"Build failed:\n```\n{output[:3000]}\n```\nFix the errors."
                    })
            
            await asyncio.sleep(0.5)
        
        return False
    
    async def _call_claude(self, messages: List[Dict], model: str) -> Optional[str]:
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
                    json={
                        "model": model,
                        "max_tokens": 8192,
                        "messages": messages
                    },
                    timeout=aiohttp.ClientTimeout(total=300)
                ) as resp:
                    if resp.status != 200:
                        return None
                    data = await resp.json()
                    content = data.get("content", [])
                    return content[0].get("text", "") if content else None
            except:
                return None
    
    async def _apply_code(self, task: Task, response: str):
        """Apply code from response to file."""
        matches = re.findall(r"```lean\n(.*?)```", response, re.DOTALL)
        if not matches:
            return
        
        file_path = HODGE_PATH / task.file_path
        file_path.parent.mkdir(parents=True, exist_ok=True)
        
        # Use largest code block
        code = max(matches, key=len)
        file_path.write_text(code)
        self.log(f"Wrote {len(code)} chars to {task.file_path}")

# =============================================================================
# Master Orchestrator
# =============================================================================

class MasterOrchestrator:
    """Manages the entire autonomous operation."""
    
    def __init__(self):
        self.tasks: Dict[str, Task] = {}
        self.paper = PaperReferenceEngine(PAPER_PATH)
        self.workers: Dict[str, WorkerAgent] = {}
        self.worker_counter = 0
        self.semaphore = asyncio.Semaphore(MAX_WORKERS)
        self.start_time = datetime.now()
        LOG_DIR.mkdir(exist_ok=True)
    
    def load_state(self):
        """Load or initialize state."""
        if STATE_FILE.exists():
            try:
                with open(STATE_FILE) as f:
                    data = json.load(f)
                for t in data.get("tasks", []):
                    task = Task.from_dict(t)
                    self.tasks[task.id] = task
                print(f"Loaded {len(self.tasks)} tasks from state")
                return
            except Exception as e:
                print(f"State load error: {e}")
        
        # Discover tasks
        for task in discover_tasks():
            self.tasks[task.id] = task
        print(f"Discovered {len(self.tasks)} tasks")
    
    def save_state(self):
        with open(STATE_FILE, "w") as f:
            json.dump({
                "tasks": [t.to_dict() for t in self.tasks.values()],
                "last_updated": datetime.now().isoformat()
            }, f, indent=2)
    
    def get_ready_tasks(self) -> List[Task]:
        """Get tasks ready to execute."""
        ready = []
        completed_ids = {t.id for t in self.tasks.values() if t.status == TaskStatus.COMPLETED}
        
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            if task.attempts >= MAX_TASK_ATTEMPTS:
                task.status = TaskStatus.FAILED
                continue
            if all(dep in completed_ids for dep in task.dependencies):
                ready.append(task)
        
        ready.sort(key=lambda t: (t.priority.value, -t.attempts))
        return ready
    
    async def run_task(self, task: Task) -> bool:
        """Run a task with a worker."""
        worker_id = f"worker_{self.worker_counter}"
        self.worker_counter += 1
        
        task.status = TaskStatus.IN_PROGRESS
        task.assigned_worker = worker_id
        task.attempts += 1
        self.save_state()
        
        worker = WorkerAgent(worker_id, self.paper)
        
        async with self.semaphore:
            success = await worker.execute(task)
        
        if success:
            task.status = TaskStatus.COMPLETED
        else:
            task.status = TaskStatus.PENDING  # Will retry
            task.last_error = "Failed after iterations"
        
        task.assigned_worker = None
        self.save_state()
        return success
    
    async def check_completion(self) -> bool:
        """Check if the proof is complete."""
        ok, output = await run_lake_build()
        if not ok:
            return False
        
        axiom_ok, axiom_output = await check_axioms()
        if axiom_ok:
            print("\n" + "=" * 60)
            print("PROOF COMPLETE!")
            print("Only standard axioms remain.")
            print("=" * 60)
            return True
        
        return False
    
    async def run(self):
        """Main autonomous loop."""
        print("=" * 60)
        print("AUTONOMOUS OPS AGENT")
        print(f"Workers: {MAX_WORKERS}")
        print(f"Paper: {PAPER_PATH}")
        print("=" * 60)
        
        if not API_KEY:
            print("ERROR: No API key found")
            return
        
        self.load_state()
        
        active: List[asyncio.Task] = []
        
        while True:
            # Check if done
            if await self.check_completion():
                print(f"\nCompleted in {datetime.now() - self.start_time}")
                break
            
            # Clean up finished tasks
            active = [t for t in active if not t.done()]
            
            # Get ready tasks
            ready = self.get_ready_tasks()
            
            # Check if stuck
            if not ready and not active:
                pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                failed = [t for t in self.tasks.values() if t.status == TaskStatus.FAILED]
                
                if not pending:
                    if failed:
                        print(f"\nStuck with {len(failed)} failed tasks")
                        # Re-attempt failed tasks with fresh state
                        for t in failed[:5]:
                            t.status = TaskStatus.PENDING
                            t.attempts = 0
                        self.save_state()
                        continue
                    else:
                        print("\nAll tasks done but proof incomplete")
                        # Rediscover
                        new_tasks = discover_tasks()
                        for t in new_tasks:
                            if t.id not in self.tasks:
                                self.tasks[t.id] = t
                        self.save_state()
                        continue
                
                await asyncio.sleep(5)
                continue
            
            # Launch workers
            slots = MAX_WORKERS - len(active)
            for task in ready[:slots]:
                print(f"Launching: {task.id}")
                active.append(asyncio.create_task(self.run_task(task)))
            
            # Status
            completed = sum(1 for t in self.tasks.values() if t.status == TaskStatus.COMPLETED)
            print(f"Active: {len(active)} | Done: {completed}/{len(self.tasks)} | Ready: {len(ready)}")
            
            await asyncio.sleep(3)
        
        # Final summary
        print("\n=== Final Summary ===")
        for status in TaskStatus:
            count = sum(1 for t in self.tasks.values() if t.status == status)
            if count:
                print(f"{status.value}: {count}")

# =============================================================================
# Entry Point
# =============================================================================

async def main():
    import sys
    if len(sys.argv) > 1:
        if sys.argv[1] == "status":
            if STATE_FILE.exists():
                with open(STATE_FILE) as f:
                    data = json.load(f)
                for t in data.get("tasks", []):
                    print(f"{t['status']:12} {t['id']}")
        elif sys.argv[1] == "reset":
            if STATE_FILE.exists():
                STATE_FILE.unlink()
            print("State reset")
    else:
        orchestrator = MasterOrchestrator()
        await orchestrator.run()

if __name__ == "__main__":
    asyncio.run(main())
