#!/usr/bin/env python3
"""
Autonomous Ops Agent for Hodge Conjecture Formalization
========================================================
Cathedral Builders, Not Bricklayers

This system is proving one of the seven Millennium Prize Problems in mathematics.
Every agent must understand they are contributing to a historic achievement:
formalizing a complete proof of the Hodge Conjecture in Lean 4.

The proof strategy (from Washburn-Barghi):
1. Every rational Hodge class can be approximated by calibrated currents
2. Calibrated currents have analytic variety support (Harvey-Lawson-King)
3. Analytic varieties in projective space are algebraic (Chow/GAGA)
4. Therefore, rational Hodge classes are algebraic

Architecture:
- Master Orchestrator: Strategic planning, paper consultation
- Worker Agents: Tactical implementation with deep mathematical understanding
- Paper Reference: The mathematical blueprint for the proof
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
MODEL = "claude-opus-4-5-20251101"  # Always use Opus 4.5 for maximum capability
MAX_WORKERS = 15  # Slightly fewer for more focused work
MAX_TASK_ATTEMPTS = 5
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "autonomous_state.json"
LOG_DIR = HODGE_PATH / "autonomous_logs"
PAPER_PATH = HODGE_PATH / "JA_hodge_approach_with_added_refs_blueCites.tex"

# CRITICAL: Files that must NEVER be overwritten - only targeted edits allowed
PROTECTED_FILES = {
    "Hodge/Kahler/Main.lean",
    "Hodge/Kahler/Microstructure.lean", 
    "Hodge/Analytic/Currents.lean",
    "Hodge/Analytic/Forms.lean",
    "Hodge/Analytic/DomCoprod.lean",
    "Hodge/Main.lean",
    "Hodge/Basic.lean",
}

# =============================================================================
# The Cathedral Vision - Shared Context for All Agents
# =============================================================================

CATHEDRAL_VISION = """
## THE HODGE CONJECTURE - What We're Building

You are contributing to a formal proof of the Hodge Conjecture, one of the 
seven Millennium Prize Problems. This is historic work.

### The Conjecture (Simplified)
On a smooth projective complex algebraic variety X, every rational (p,p)-Hodge 
class is a rational linear combination of classes of algebraic cycles.

### Our Proof Strategy (Washburn-Barghi Approach)
1. **Calibration-Coercivity**: The Kähler form ω^p/p! is a calibration. 
   Rational Hodge classes can be approximated by currents with vanishing 
   calibration defect.

2. **Harvey-Lawson-King Structure Theorem**: Calibrated integral currents 
   are supported on analytic varieties.

3. **Chow's Theorem + GAGA**: Closed analytic subvarieties of projective 
   space are algebraic.

4. **Conclusion**: Rational Hodge classes are algebraic.

### The Codebase Structure
- `Hodge/Kahler/Main.lean` - The main theorem `hodge_conjecture'`
- `Hodge/Analytic/` - Currents, forms, test functions, distributions
- `Hodge/Classical/` - Harvey-Lawson, GAGA, Chow theorems
- `Hodge/GMT/` - Geometric measure theory (mass, flat norm)
- `Hodge/Cohomology/` - de Rham, cycle classes

### Your Role
You are not just writing code. You are:
- Translating deep mathematics into formal proofs
- Building infrastructure that connects to Mathlib
- Ensuring every definition captures the true mathematical content
- Creating something that will be verified by a computer and trusted forever

Think like a mathematician formalizing their life's work. Every `sorry` you 
eliminate is a step toward completing a Millennium Prize proof.
"""

# =============================================================================
# Data Structures
# =============================================================================

class TaskStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"

class TaskPriority(int, Enum):
    CRITICAL = 0
    HIGH = 1
    MEDIUM = 2
    LOW = 3

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
    paper_context: Optional[str] = None
    
    def to_dict(self):
        d = asdict(self)
        d["status"] = self.status.value
        d["priority"] = self.priority.value
        return d
    
    @classmethod
    def from_dict(cls, d):
        d["status"] = TaskStatus(d["status"])
        d["priority"] = TaskPriority(d.get("priority", 2))
        return cls(**{k: v for k, v in d.items() if k in cls.__dataclass_fields__})

# =============================================================================
# Paper Reference Engine
# =============================================================================

class PaperEngine:
    """Parses the mathematical paper for guidance."""
    
    def __init__(self, path: Path):
        self.path = path
        self.content = ""
        self.sections = {}
        if path.exists():
            self.content = path.read_text(errors="ignore")
            self._parse_sections()
            print(f"Paper loaded: {len(self.content)} chars, {len(self.sections)} sections")
    
    def _parse_sections(self):
        pattern = r"\\section\{([^}]+)\}(.*?)(?=\\section|\\end\{document\}|$)"
        for m in re.finditer(pattern, self.content, re.DOTALL):
            self.sections[m.group(1).strip()] = m.group(2)[:3000]
    
    def get_context(self, query: str, max_chars: int = 6000) -> str:
        """Get relevant paper content for a query."""
        query_words = set(query.lower().split())
        relevant = []
        
        for title, content in self.sections.items():
            if any(w in title.lower() for w in query_words):
                relevant.append(f"=== {title} ===\n{content[:2000]}")
        
        if not relevant:
            # Search in content
            for title, content in self.sections.items():
                if any(w in content.lower() for w in query_words):
                    relevant.append(f"=== {title} ===\n{content[:1500]}")
        
        result = "\n\n".join(relevant[:3])
        return result[:max_chars] if result else self.content[:max_chars]

# =============================================================================
# Build System
# =============================================================================

async def run_build(file_path: str = None) -> Tuple[bool, str]:
    """Run lake build."""
    try:
        # Cache first
        await asyncio.create_subprocess_exec(
            "lake", "exe", "cache", "get",
            cwd=str(HODGE_PATH),
            stdout=asyncio.subprocess.DEVNULL,
            stderr=asyncio.subprocess.DEVNULL
        )
        
        cmd = ["lake", "build"]
        proc = await asyncio.create_subprocess_exec(
            *cmd, cwd=str(HODGE_PATH),
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        stdout, stderr = await asyncio.wait_for(proc.communicate(), timeout=600)
        output = (stdout + stderr).decode()
        return proc.returncode == 0, output
    except Exception as e:
        return False, str(e)

# =============================================================================
# Task Discovery
# =============================================================================

def discover_tasks() -> List[Task]:
    """Discover tasks from the codebase - scaffold files that need work."""
    tasks = []
    
    # Stage scaffold files that need implementation
    scaffolds = [
        ("stage1_testforms", "Hodge/Analytic/Stage1/TestForms.lean", 
         "Implement LF-space test forms with proper Mathlib integration"),
        ("stage1_deriv", "Hodge/Analytic/Stage1/EuclidTestFormsDeriv.lean",
         "Implement exterior derivative as continuous linear map on test forms"),
        ("stage2_integration", "Hodge/Analytic/Stage2/IntegrationCurrentsReal.lean",
         "Implement integration currents [Z](ω) = ∫_Z ι*ω using Mathlib"),
        ("stage3_mass", "Hodge/Analytic/MassReal.lean",
         "Implement proper mass definition via dual norm"),
        ("stage3_flatnorm", "Hodge/Analytic/FlatNormReal.lean",
         "Implement flat norm F(T) = inf{M(R) + M(S) : T = R + ∂S}"),
        ("stage4_calibration", "Hodge/Analytic/CalibrationReal.lean",
         "Implement calibration theory connecting to Kähler geometry"),
        ("stage5_gaga", "Hodge/AlgGeom/GAGAReal.lean",
         "Implement GAGA theorem infrastructure"),
        ("stage6_cohomology", "Hodge/Cohomology/CohomologyReal.lean",
         "Implement cohomology bridge and cycle class maps"),
    ]
    
    for task_id, file_path, desc in scaffolds:
        full_path = HODGE_PATH / file_path
        if full_path.exists():
            # Check if it's still a scaffold (has placeholder content)
            content = full_path.read_text()
            if "placeholder" in content.lower() or "Float" in content or len(content) < 500:
                tasks.append(Task(
                    id=task_id,
                    description=desc,
                    file_path=file_path,
                    target="implement_real_content",
                    priority=TaskPriority.HIGH
                ))
    
    return tasks

# =============================================================================
# Worker Agent
# =============================================================================

class Worker:
    """Cathedral builder - understands the grand vision."""
    
    def __init__(self, worker_id: str, paper: PaperEngine):
        self.id = worker_id
        self.paper = paper
        self.log_file = LOG_DIR / f"{worker_id}.log"
    
    def log(self, msg: str):
        line = f"[{datetime.now():%H:%M:%S}] {msg}\n"
        with open(self.log_file, "a") as f:
            f.write(line)
        print(f"[{self.id}] {msg}")
    
    async def execute(self, task: Task) -> bool:
        self.log(f"Starting: {task.description}")
        
        # Get paper context
        paper_context = self.paper.get_context(task.description)
        
        # Read current file
        file_path = HODGE_PATH / task.file_path
        current_content = ""
        if file_path.exists():
            current_content = file_path.read_text()
        
        # Build the cathedral prompt
        prompt = self._build_prompt(task, paper_context, current_content)
        
        messages = [{"role": "user", "content": prompt}]
        
        for iteration in range(8):
            self.log(f"Iteration {iteration + 1}")
            
            response = await self._call_api(messages)
            if not response:
                await asyncio.sleep(2)
                continue
            
            messages.append({"role": "assistant", "content": response})
            
            # Extract and apply code
            if "```lean" in response:
                new_content = self._extract_code(response)
                if new_content and len(new_content) > 100:
                    # Safety check for protected files
                    if task.file_path in PROTECTED_FILES:
                        self.log(f"PROTECTED FILE - not overwriting {task.file_path}")
                    else:
                        file_path.parent.mkdir(parents=True, exist_ok=True)
                        file_path.write_text(new_content)
                        self.log(f"Wrote {len(new_content)} chars")
            
            # Check for completion
            if "TASK_COMPLETE" in response:
                ok, output = await run_build()
                if ok:
                    self.log("BUILD SUCCESS!")
                    return True
                else:
                    self.log(f"Build failed, iterating...")
                    messages.append({
                        "role": "user", 
                        "content": f"Build failed:\n```\n{output[:2500]}\n```\n\nFix the errors. Remember the cathedral we're building."
                    })
            
            await asyncio.sleep(0.5)
        
        self.log("Max iterations reached")
        return False
    
    def _build_prompt(self, task: Task, paper_context: str, current_content: str) -> str:
        return f"""{CATHEDRAL_VISION}

---

## YOUR CURRENT TASK

**Task:** {task.description}
**File:** {task.file_path}
**Target:** {task.target}

### Mathematical Reference (from the proof paper)
{paper_context}

### Current File Content
```lean
{current_content[:4000]}
```

---

## INSTRUCTIONS

You are building a critical piece of the Hodge Conjecture formalization.

1. **Understand the mathematics first** - What does this component represent?
2. **Connect to Mathlib** - Use existing Mathlib structures where possible
3. **Write real definitions** - No `Float`, no trivial placeholders
4. **Prove what you can** - Use `sorry` only for genuinely deep results
5. **Document thoroughly** - Future mathematicians will read this

When you have a complete, compiling implementation, say "TASK_COMPLETE".

The code must:
- Import from Mathlib appropriately
- Use proper Lean 4 syntax
- Build successfully with `lake build`
- Represent the actual mathematical content

Begin. Think deeply. Build the cathedral.
"""
    
    def _extract_code(self, response: str) -> Optional[str]:
        matches = re.findall(r"```lean\n(.*?)```", response, re.DOTALL)
        if matches:
            return max(matches, key=len)
        return None
    
    async def _call_api(self, messages: List[Dict]) -> Optional[str]:
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
                        "model": MODEL,
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
            except Exception as e:
                print(f"API error: {e}")
                return None

# =============================================================================
# Master Orchestrator  
# =============================================================================

class Orchestrator:
    """The architect overseeing the cathedral construction."""
    
    def __init__(self):
        self.tasks: Dict[str, Task] = {}
        self.paper = PaperEngine(PAPER_PATH)
        self.semaphore = asyncio.Semaphore(MAX_WORKERS)
        self.worker_count = 0
        LOG_DIR.mkdir(exist_ok=True)
    
    def load_state(self):
        if STATE_FILE.exists():
            try:
                data = json.loads(STATE_FILE.read_text())
                for t in data.get("tasks", []):
                    task = Task.from_dict(t)
                    self.tasks[task.id] = task
                print(f"Loaded {len(self.tasks)} tasks")
                return
            except Exception as e:
                print(f"State load error: {e}")
        
        for task in discover_tasks():
            self.tasks[task.id] = task
        print(f"Discovered {len(self.tasks)} tasks")
    
    def save_state(self):
        STATE_FILE.write_text(json.dumps({
            "tasks": [t.to_dict() for t in self.tasks.values()],
            "updated": datetime.now().isoformat()
        }, indent=2))
    
    def get_ready_tasks(self) -> List[Task]:
        completed = {t.id for t in self.tasks.values() if t.status == TaskStatus.COMPLETED}
        ready = []
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            if task.attempts >= MAX_TASK_ATTEMPTS:
                task.status = TaskStatus.FAILED
                continue
            if all(d in completed for d in task.dependencies):
                ready.append(task)
        ready.sort(key=lambda t: t.priority.value)
        return ready
    
    async def run_task(self, task: Task) -> bool:
        worker_id = f"worker_{self.worker_count}"
        self.worker_count += 1
        
        task.status = TaskStatus.IN_PROGRESS
        task.attempts += 1
        self.save_state()
        
        worker = Worker(worker_id, self.paper)
        
        async with self.semaphore:
            success = await worker.execute(task)
        
        task.status = TaskStatus.COMPLETED if success else TaskStatus.PENDING
        self.save_state()
        return success
    
    async def run(self):
        print("=" * 60)
        print("HODGE CONJECTURE - CATHEDRAL BUILDERS")
        print(f"Model: {MODEL}")
        print(f"Workers: {MAX_WORKERS}")
        print("=" * 60)
        
        if not API_KEY:
            print("ERROR: No API key")
            return
        
        self.load_state()
        
        # Reset any stuck in_progress tasks
        for task in self.tasks.values():
            if task.status == TaskStatus.IN_PROGRESS:
                task.status = TaskStatus.PENDING
        self.save_state()
        
        active: List[asyncio.Task] = []
        
        while True:
            active = [t for t in active if not t.done()]
            ready = self.get_ready_tasks()
            
            if not ready and not active:
                pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                if not pending:
                    print("\n" + "=" * 60)
                    print("ALL TASKS COMPLETE - THE CATHEDRAL STANDS")
                    print("=" * 60)
                    break
                await asyncio.sleep(5)
                continue
            
            for task in ready[:MAX_WORKERS - len(active)]:
                print(f"Launching: {task.id}")
                active.append(asyncio.create_task(self.run_task(task)))
            
            completed = sum(1 for t in self.tasks.values() if t.status == TaskStatus.COMPLETED)
            print(f"Progress: {completed}/{len(self.tasks)} | Active: {len(active)} | Ready: {len(ready)}")
            
            await asyncio.sleep(3)

# =============================================================================
# Entry Point
# =============================================================================

if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "status":
        if STATE_FILE.exists():
            data = json.loads(STATE_FILE.read_text())
            for t in data.get("tasks", []):
                print(f"{t['status']:12} {t['id']}")
    elif len(sys.argv) > 1 and sys.argv[1] == "reset":
        STATE_FILE.unlink(missing_ok=True)
        print("State reset")
    else:
        asyncio.run(Orchestrator().run())
