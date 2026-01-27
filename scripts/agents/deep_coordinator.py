#!/usr/bin/env python3
"""
Deep Mode Coordinator - Agents with file access and Lean compilation
=====================================================================
Each agent can read/write files, run lake build, and iterate until success.
"""

import os
import json
import asyncio
import aiohttp
import subprocess
from dataclasses import dataclass, field, asdict
from datetime import datetime
from pathlib import Path
from typing import Optional, List, Dict, Any, Tuple
from enum import Enum
import traceback

def _load_anthropic_api_key() -> str:
    """Load Anthropic API key from env, with a safe on-disk fallback on the server."""
    key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    if key:
        return key
    # Fallback paths (avoid putting secrets in process args)
    home = Path.home()
    candidates = [
        home / ".anthropic_api_key",
        home / ".config" / "hodge" / "anthropic_api_key",
    ]
    for p in candidates:
        try:
            if p.exists():
                v = p.read_text().strip()
                if v:
                    return v
        except Exception:
            continue
    return ""


ANTHROPIC_API_KEY = _load_anthropic_api_key()
MODEL = "claude-sonnet-4-20250514"
MAX_CONCURRENT_AGENTS = 6  # Run more agents in parallel for Phase 2
MAX_ITERATIONS = 20  # More iterations per task
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "deep_agent_state.json"
LOG_DIR = HODGE_PATH / "deep_agent_logs"


class TaskStatus(str, Enum):
    PENDING = "pending"
    IN_PROGRESS = "in_progress"
    COMPLETED = "completed"
    FAILED = "failed"


@dataclass
class Task:
    id: str
    description: str
    file_path: str
    target: str
    status: TaskStatus = TaskStatus.PENDING
    dependencies: List[str] = field(default_factory=list)
    iterations: int = 0
    result: Optional[str] = None
    error: Optional[str] = None

    def to_dict(self):
        d = asdict(self)
        d['status'] = self.status.value
        return d

    @classmethod
    def from_dict(cls, d):
        d['status'] = TaskStatus(d['status'])
        return cls(**d)


# Phase 5: Replace trivial universal instances with real implementations
# The goal is to make the proof non-vacuous (so the critic on Zulip has no complaint)
TASKS = [
    # 1. AutomaticSYRData.universal currently returns zero current
    # Replace with non-trivial microstructure sequence construction
    Task(
        id="automatic_syr_nontrivial",
        description="Replace AutomaticSYRData.universal with a non-trivial microstructure construction that actually builds currents from sheets",
        file_path="Hodge/Kahler/Main.lean",
        target="AutomaticSYRData.universal"
    ),
    # 2. HarveyLawsonKingData.universal returns empty varieties
    # Replace with real analytic decomposition
    Task(
        id="harvey_lawson_nontrivial",
        description="Replace HarveyLawsonKingData.universal with a construction that extracts analytic varieties from calibrated currents (not empty set)",
        file_path="Hodge/Classical/HarveyLawson.lean",
        target="HarveyLawsonKingData.universal"
    ),
    # 3. PoincareDualFormExists needs a universal instance that returns actual forms
    Task(
        id="poincare_dual_universal",
        description="Create PoincareDualFormExists.universal instance that returns omega^p for non-empty sets (not zero)",
        file_path="Hodge/Classical/CycleClass.lean",
        target="PoincareDualFormExists"
    ),
    # 4. SpineBridgeData.universal - bridge geometric class to representing form
    Task(
        id="spine_bridge_universal",
        description="Create SpineBridgeData.universal instance that proves fundamental_eq_representing",
        file_path="Hodge/Classical/GAGA.lean",
        target="SpineBridgeData"
    ),
    # 5. Validate entire proof after above changes
    Task(
        id="validate_full_proof",
        description="Verify hodge_conjecture' compiles and check axioms only show standard 3",
        file_path="Hodge/Kahler/Main.lean",
        target="hodge_conjecture'",
        dependencies=["automatic_syr_nontrivial", "harvey_lawson_nontrivial", 
                      "poincare_dual_universal", "spine_bridge_universal"]
    ),
]


TOOLS = [
    {
        "name": "read_file",
        "description": "Read a Lean file from the repository",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string", "description": "Path relative to repo root"},
                "start_line": {"type": "integer", "description": "Optional 1-based start line"},
                "end_line": {"type": "integer", "description": "Optional 1-based end line (inclusive)"},
                "max_chars": {"type": "integer", "description": "Optional max chars to return"}
            },
            "required": ["path"]
        }
    },
    {
        "name": "write_file",
        "description": "Write/overwrite a file",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "content": {"type": "string"}
            },
            "required": ["path", "content"]
        }
    },
    {
        "name": "search_replace",
        "description": "Replace a string in a file (must be unique match)",
        "input_schema": {
            "type": "object",
            "properties": {
                "path": {"type": "string"},
                "old_string": {"type": "string", "description": "Exact string to find"},
                "new_string": {"type": "string", "description": "Replacement string"}
            },
            "required": ["path", "old_string", "new_string"]
        }
    },
    {
        "name": "run_lake_build",
        "description": "Run lake build on a specific module or the whole project",
        "input_schema": {
            "type": "object",
            "properties": {
                "module": {"type": "string", "description": "Optional: specific module like Hodge.Classical.GAGA"}
            }
        }
    },
    {
        "name": "check_axioms",
        "description": "Check what axioms a theorem depends on",
        "input_schema": {
            "type": "object",
            "properties": {
                "theorem": {"type": "string", "description": "Fully qualified theorem name"}
            },
            "required": ["theorem"]
        }
    },
    {
        "name": "grep",
        "description": "Search for a pattern in .lean files",
        "input_schema": {
            "type": "object",
            "properties": {
                "pattern": {"type": "string"},
                "path": {"type": "string", "description": "Subdirectory to search, default Hodge/"}
            },
            "required": ["pattern"]
        }
    },
    {
        "name": "task_complete",
        "description": "Mark the task as complete with a summary",
        "input_schema": {
            "type": "object",
            "properties": {
                "success": {"type": "boolean"},
                "summary": {"type": "string"},
                "changes_made": {"type": "string"}
            },
            "required": ["success", "summary"]
        }
    }
]


def execute_tool(name: str, input_data: Dict) -> Dict:
    """Execute a tool and return result."""
    try:
        if name == "read_file":
            path = HODGE_PATH / input_data["path"]
            if not path.exists():
                return {"error": f"File not found: {path}"}
            content = path.read_text()

            # Optional line slicing for large files
            if "start_line" in input_data or "end_line" in input_data:
                lines = content.splitlines()
                total = len(lines)
                start_line = int(input_data.get("start_line", 1) or 1)
                end_line = input_data.get("end_line", None)
                if end_line is None:
                    end_line = start_line + 200  # default window
                end_line = int(end_line)
                start_line = max(1, start_line)
                end_line = max(start_line, end_line)
                start_idx = start_line - 1
                end_idx = min(total, end_line)
                sliced = "\n".join(lines[start_idx:end_idx])
                max_chars = input_data.get("max_chars", None)
                if max_chars is not None:
                    sliced = sliced[: int(max_chars)]
                return {
                    "content": sliced,
                    "start_line": start_line,
                    "end_line": end_idx,
                    "total_lines": total,
                }

            # Truncate if too long
            max_chars = int(input_data.get("max_chars", 50000) or 50000)
            if len(content) > max_chars:
                content = content[:max_chars] + "\n... [truncated]"
            return {"content": content}

        elif name == "write_file":
            path = HODGE_PATH / input_data["path"]
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(input_data["content"])
            return {"success": True, "message": f"Wrote {len(input_data['content'])} chars"}

        elif name == "search_replace":
            path = HODGE_PATH / input_data["path"]
            if not path.exists():
                return {"error": f"File not found: {path}"}
            content = path.read_text()
            old = input_data["old_string"]
            new = input_data["new_string"]
            if old not in content:
                return {"error": f"String not found. First 200 chars of file:\n{content[:200]}"}
            if content.count(old) > 1:
                return {"error": f"String appears {content.count(old)} times, must be unique"}
            new_content = content.replace(old, new, 1)
            path.write_text(new_content)
            return {"success": True}

        elif name == "run_lake_build":
            module = input_data.get("module", "")
            # Workspace rule: NEVER rebuild Mathlib from source.
            # Always fetch Mathlib cache before any `lake build`.
            cache = subprocess.run(
                ["lake", "exe", "cache", "get"],
                cwd=HODGE_PATH, capture_output=True, text=True, timeout=900
            )

            cmd = ["lake", "build"]
            if module:
                cmd.append(module)
            result = subprocess.run(
                cmd, cwd=HODGE_PATH, capture_output=True, text=True, timeout=600
            )
            output = (cache.stdout + cache.stderr + result.stdout + result.stderr)[-8000:]  # Last 8k chars
            return {
                "success": result.returncode == 0,
                "output": output
            }

        elif name == "check_axioms":
            theorem = input_data["theorem"]
            check_code = f"import Hodge\n#print axioms {theorem}"
            check_file = HODGE_PATH / "_check.lean"
            check_file.write_text(check_code)
            result = subprocess.run(
                ["lake", "env", "lean", str(check_file)],
                cwd=HODGE_PATH, capture_output=True, text=True, timeout=120
            )
            check_file.unlink(missing_ok=True)
            return {"output": result.stdout + result.stderr}

        elif name == "grep":
            pattern = input_data["pattern"]
            search_path = input_data.get("path", "Hodge/")
            result = subprocess.run(
                ["grep", "-rn", "--include=*.lean", pattern, str(HODGE_PATH / search_path)],
                capture_output=True, text=True, timeout=30
            )
            output = result.stdout[-5000:] if result.stdout else "No matches"
            return {"matches": output}

        elif name == "task_complete":
            return {"done": True, **input_data}

        else:
            return {"error": f"Unknown tool: {name}"}

    except subprocess.TimeoutExpired:
        return {"error": "Command timed out"}
    except Exception as e:
        return {"error": str(e)}


class DeepCoordinator:
    def __init__(self):
        self.tasks: Dict[str, Task] = {}
        self.session: Optional[aiohttp.ClientSession] = None
        self.session_id = datetime.now().strftime("%Y%m%d_%H%M%S")
        self.backup_dir = HODGE_PATH / "deep_agent_backups" / self.session_id
        self.load_state()

    def load_state(self):
        if STATE_FILE.exists():
            with open(STATE_FILE) as f:
                data = json.load(f)
                self.tasks = {k: Task.from_dict(v) for k, v in data.get('tasks', {}).items()}
        else:
            for task in TASKS:
                self.tasks[task.id] = task
        LOG_DIR.mkdir(parents=True, exist_ok=True)
        self.backup_dir.mkdir(parents=True, exist_ok=True)

    def save_state(self):
        with open(STATE_FILE, 'w') as f:
            json.dump({
                'tasks': {k: v.to_dict() for k, v in self.tasks.items()},
                'updated': datetime.now().isoformat()
            }, f, indent=2)

    async def call_claude(self, messages: List[Dict], system: str) -> Dict:
        headers = {
            "x-api-key": ANTHROPIC_API_KEY,
            "content-type": "application/json",
            "anthropic-version": "2023-06-01"
        }
        payload = {
            "model": MODEL,
            "max_tokens": 8192,
            "system": system,
            "messages": messages,
            "tools": TOOLS
        }
        timeout = aiohttp.ClientTimeout(total=300)  # 5 minute timeout
        async with self.session.post(
            "https://api.anthropic.com/v1/messages",
            headers=headers,
            json=payload,
            timeout=timeout
        ) as resp:
            if resp.status != 200:
                raise Exception(f"API error {resp.status}: {await resp.text()}")
            return await resp.json()

    async def work_on_task(self, task: Task) -> bool:
        """Deep work on a task with tool use."""
        task.status = TaskStatus.IN_PROGRESS
        self.save_state()

        # Per-task backups to prevent corrupted state when an agent fails.
        # Maps relative path -> (existed_before, previous_content)
        backups: Dict[str, Tuple[bool, Optional[str]]] = {}

        def backup_path(rel_path: str) -> None:
            if rel_path in backups:
                return
            abs_path = HODGE_PATH / rel_path
            if abs_path.exists():
                backups[rel_path] = (True, abs_path.read_text())
            else:
                backups[rel_path] = (False, None)

        def restore_backups() -> None:
            for rel_path, (existed, content) in backups.items():
                abs_path = HODGE_PATH / rel_path
                try:
                    if existed:
                        abs_path.parent.mkdir(parents=True, exist_ok=True)
                        abs_path.write_text(content or "")
                    else:
                        abs_path.unlink(missing_ok=True)
                except Exception:
                    # Best-effort restore; keep going.
                    continue

        # Verified/deep mode system prompt (NO `sorry` allowed).
        system = f"""You are an expert Lean 4 mathematician working on the Hodge Conjecture formalization.

YOUR TASK: {task.description}
TARGET: {task.target} in {task.file_path}

HARD REQUIREMENTS:
- Do NOT use `sorry`, `admit`, or introduce `axiom`s.
- Do NOT "paper over" missing theory with semantic stubs (e.g. `integral := 0`) unless it is
  genuinely the mathematically correct value for the object in question.
- Keep the project building (use `run_lake_build` frequently; prefer module-level builds).

If the task involves removing a stubbed *instance*, you may:
- Remove the instance and make the dependency explicit by adding a typeclass parameter where needed, OR
- Replace the stub by a new interface (typeclass/structure field) that precisely captures the missing theorem,
  but do not fake an implementation.

WORKFLOW:
1. Read the target file (use line ranges for large files).
2. Make small, targeted edits with `search_replace` (prefer minimal diffs).
3. Run `run_lake_build` on the affected module and iterate until it passes.
4. When done, call `task_complete(success=true, summary=..., changes_made=...)`.

You have up to {MAX_ITERATIONS} tool calls.
"""

        messages = [{
            "role": "user",
            "content": f"Please work on: {task.description}\n\nStart by reading {task.file_path}"
        }]

        log_file = LOG_DIR / f"{task.id}_{datetime.now().strftime('%H%M%S')}.log"
        log_lines = [f"Task: {task.id}", f"Start: {datetime.now().isoformat()}", ""]

        try:
            for iteration in range(MAX_ITERATIONS):
                task.iterations = iteration + 1
                self.save_state()

                response = await self.call_claude(messages, system)
                content = response.get("content", [])

                # Log the response
                log_lines.append(f"=== Iteration {iteration + 1} ===")

                # Check for tool use
                tool_uses = [c for c in content if c.get("type") == "tool_use"]
                text_parts = [c.get("text", "") for c in content if c.get("type") == "text"]

                for text in text_parts:
                    if text:
                        log_lines.append(f"Claude: {text[:500]}...")

                if not tool_uses:
                    # No more tool calls, check if done
                    log_lines.append("No tool calls, ending")
                    break

                # Add assistant message
                messages.append({"role": "assistant", "content": content})

                # Execute tools
                tool_results = []
                for tool_use in tool_uses:
                    tool_name = tool_use["name"]
                    tool_input = tool_use["input"]
                    log_lines.append(f"Tool: {tool_name}({json.dumps(tool_input)[:200]})")

                    # Backup any file about to be modified.
                    if tool_name in ("write_file", "search_replace"):
                        try:
                            backup_path(tool_input.get("path", ""))
                        except Exception:
                            pass

                    result = execute_tool(tool_name, tool_input)
                    log_lines.append(f"Result: {json.dumps(result)[:300]}")

                    tool_results.append({
                        "type": "tool_result",
                        "tool_use_id": tool_use["id"],
                        "content": json.dumps(result)
                    })

                    # Check if task_complete was called
                    if tool_name == "task_complete":
                        task.result = tool_input.get("summary", "")
                        if tool_input.get("success"):
                            task.status = TaskStatus.COMPLETED
                        else:
                            task.status = TaskStatus.FAILED
                            task.error = tool_input.get("summary", "Failed")
                            restore_backups()
                        self.save_state()
                        log_file.write_text("\n".join(log_lines))
                        return task.status == TaskStatus.COMPLETED

                messages.append({"role": "user", "content": tool_results})

            # Max iterations reached
            task.status = TaskStatus.FAILED
            task.error = f"Max iterations ({MAX_ITERATIONS}) reached"
            restore_backups()

        except Exception as e:
            task.status = TaskStatus.FAILED
            task.error = str(e)
            restore_backups()
            log_lines.append(f"Error: {traceback.format_exc()}")

        self.save_state()
        log_file.write_text("\n".join(log_lines))
        return False

    def get_ready_tasks(self) -> List[Task]:
        ready = []
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            deps_met = all(
                (dep in self.tasks) and (self.tasks[dep].status == TaskStatus.COMPLETED)
                for dep in task.dependencies
            )
            if deps_met:
                ready.append(task)
        return ready

    def propagate_dependency_failures(self) -> bool:
        """Mark tasks as failed if they are blocked by missing/failed dependencies."""
        changed = False
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING:
                continue
            for dep in task.dependencies:
                if dep not in self.tasks:
                    task.status = TaskStatus.FAILED
                    task.error = f"Missing dependency: {dep}"
                    changed = True
                    break
                if self.tasks[dep].status == TaskStatus.FAILED:
                    task.status = TaskStatus.FAILED
                    task.error = f"Dependency failed: {dep}"
                    changed = True
                    break
        if changed:
            self.save_state()
        return changed

    async def run(self):
        print(f"Deep Coordinator starting")
        print(f"Tasks: {len(self.tasks)}")
        self.session = aiohttp.ClientSession()

        try:
            while True:
                # Avoid infinite waiting when a dependency has already failed.
                self.propagate_dependency_failures()
                ready = self.get_ready_tasks()
                if not ready:
                    pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                    if not pending:
                        print("All tasks done!")
                        break
                    print(f"Waiting for dependencies... ({len(pending)} pending)")
                    await asyncio.sleep(5)
                    continue

                # Run up to MAX_CONCURRENT_AGENTS
                batch = ready[:MAX_CONCURRENT_AGENTS]
                print(f"Running {len(batch)} tasks: {[t.id for t in batch]}")

                results = await asyncio.gather(
                    *[self.work_on_task(t) for t in batch],
                    return_exceptions=True
                )

                for task, result in zip(batch, results):
                    if isinstance(result, Exception):
                        print(f"  {task.id}: ERROR - {result}")
                    else:
                        print(f"  {task.id}: {'SUCCESS' if result else 'FAILED'}")

        finally:
            await self.session.close()
            self.save_state()

    def status(self):
        lines = ["# Deep Mode Status", ""]
        by_status = {}
        for task in self.tasks.values():
            by_status.setdefault(task.status.value, []).append(task)
        for status, tasks in sorted(by_status.items()):
            lines.append(f"## {status.upper()} ({len(tasks)})")
            for t in tasks:
                lines.append(f"- {t.id}: {t.description} [iter: {t.iterations}]")
                if t.error:
                    lines.append(f"  Error: {t.error}")
            lines.append("")
        return "\n".join(lines)


async def main():
    import sys
    coord = DeepCoordinator()

    if len(sys.argv) > 1 and sys.argv[1] == "status":
        print(coord.status())
        return

    if len(sys.argv) > 1 and sys.argv[1] == "reset":
        STATE_FILE.unlink(missing_ok=True)
        print("State reset")
        return

    await coord.run()


if __name__ == "__main__":
    asyncio.run(main())
