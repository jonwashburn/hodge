#!/usr/bin/env python3
"""
Massive Parallel Coordinator - 25+ Agents for Hodge Conjecture Formalization
=============================================================================
Orchestrates 20-30 Claude instances to parallelize the Lean 4 formalization work.
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


def _load_anthropic_api_key():
    key = (os.environ.get("ANTHROPIC_API_KEY") or "").strip()
    if key:
        return key
    home = Path.home()
    for p in [home / ".anthropic_api_key", home / ".anthropic_key"]:
        try:
            if p.exists():
                return p.read_text().strip()
        except:
            pass
    return ""


ANTHROPIC_API_KEY = _load_anthropic_api_key()
MODEL = "claude-opus-4-5-20251101"
MAX_CONCURRENT_AGENTS = 25
MAX_ITERATIONS = 15
HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "massive_parallel_state.json"
LOG_DIR = HODGE_PATH / "massive_parallel_logs"
TASK_FILE = HODGE_PATH / "scripts/agents/stage1_parallel_tasks.json"


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
    stage: int = 0
    track: str = ""
    status: TaskStatus = TaskStatus.PENDING
    dependencies: List[str] = field(default_factory=list)
    priority: int = 0
    iterations: int = 0
    result: Optional[str] = None
    error: Optional[str] = None

    def to_dict(self):
        d = asdict(self)
        d["status"] = self.status.value
        return d

    @classmethod
    def from_dict(cls, d):
        d["status"] = TaskStatus(d["status"])
        return cls(**d)


def load_tasks_from_json():
    if not TASK_FILE.exists():
        return []
    with open(TASK_FILE) as f:
        data = json.load(f)
    return [Task(
        id=t["id"], description=t["description"], file_path=t["file_path"],
        target=t["target"], stage=t.get("stage", 0), track=t.get("track", ""),
        dependencies=t.get("dependencies", []), priority=t.get("priority", 0)
    ) for t in data.get("tasks", [])]


class Coordinator:
    def __init__(self):
        self.tasks = {}
        self.completed = set()
        self.in_progress = set()
        self.counter = 0
        self.semaphore = asyncio.Semaphore(MAX_CONCURRENT_AGENTS)
        self.file_locks = {}
        LOG_DIR.mkdir(exist_ok=True)

    def load_state(self):
        if STATE_FILE.exists():
            try:
                with open(STATE_FILE) as f:
                    data = json.load(f)
                for t in data.get("tasks", []):
                    task = Task.from_dict(t)
                    self.tasks[task.id] = task
                    if task.status == TaskStatus.COMPLETED:
                        self.completed.add(task.id)
                print(f"Loaded: {len(self.completed)} done, {len(self.tasks)} total")
                return
            except Exception as e:
                print(f"Load error: {e}")
        for task in load_tasks_from_json():
            self.tasks[task.id] = task
        print(f"Initialized {len(self.tasks)} tasks")

    def save_state(self):
        with open(STATE_FILE, "w") as f:
            json.dump({"tasks": [t.to_dict() for t in self.tasks.values()]}, f, indent=2)

    def get_ready(self):
        ready = []
        for task in self.tasks.values():
            if task.status != TaskStatus.PENDING or task.id in self.in_progress:
                continue
            if all(self.tasks.get(d, Task(id=d, description="", file_path="", target="")).status == TaskStatus.COMPLETED for d in task.dependencies):
                ready.append(task)
        ready.sort(key=lambda t: t.priority)
        return ready

    async def run_agent(self, task):
        agent_id = f"agent_{self.counter}"
        self.counter += 1
        task.status = TaskStatus.IN_PROGRESS
        self.in_progress.add(task.id)
        self.save_state()

        log_file = LOG_DIR / f"{task.id}.log"
        def log(msg):
            line = f"[{datetime.now():%H:%M:%S}] {msg}\n"
            with open(log_file, "a") as f:
                f.write(line)
            print(f"[{agent_id}] {msg}")

        log(f"Starting: {task.description}")

        try:
            async with self.semaphore:
                success = await self._agent_loop(task, log)
            task.status = TaskStatus.COMPLETED if success else TaskStatus.FAILED
            if success:
                self.completed.add(task.id)
                log("COMPLETED!")
            else:
                log("FAILED")
        except Exception as e:
            task.status = TaskStatus.FAILED
            task.error = str(e)
            log(f"Exception: {e}")
        finally:
            self.in_progress.discard(task.id)
            self.save_state()
        return task.status == TaskStatus.COMPLETED

    async def _agent_loop(self, task, log):
        prompt = self._build_prompt(task)
        messages = [{"role": "user", "content": prompt}]

        for i in range(MAX_ITERATIONS):
            task.iterations = i + 1
            log(f"Iteration {i+1}/{MAX_ITERATIONS}")

            resp = await self._call_claude(messages)
            if not resp:
                await asyncio.sleep(2)
                continue

            messages.append({"role": "assistant", "content": resp})

            if "TASK_COMPLETE" in resp:
                ok, out = await self._build(task.file_path)
                if ok:
                    return True
                messages.append({"role": "user", "content": f"Build failed:\n{out[:2000]}"})

            if "```lean" in resp:
                await self._apply_code(task, resp, log)
                ok, out = await self._build(task.file_path)
                if ok:
                    return True
                messages.append({"role": "user", "content": f"Build failed:\n{out[:2000]}"})

            await asyncio.sleep(0.5)
        return False

    def _build_prompt(self, task):
        if task.track == "scaffold":
            return f"""Create scaffold file for Hodge formalization.

TASK: {task.description}
FILE: {task.file_path}
TARGET: {task.target}

Create a Lean 4 file with proper imports, module docs, type definitions, and theorem statements (can use sorry). Must compile.

Say "TASK_COMPLETE" when done."""
        return f"""Implement for Hodge formalization.

TASK: {task.description}
FILE: {task.file_path}
TARGET: {task.target}
STAGE: {task.stage}

Implement with real proofs where possible. Must compile with lake build.

Say "TASK_COMPLETE" when done."""

    async def _call_claude(self, messages):
        if not ANTHROPIC_API_KEY:
            return None
        async with aiohttp.ClientSession() as session:
            try:
                async with session.post(
                    "https://api.anthropic.com/v1/messages",
                    headers={"x-api-key": ANTHROPIC_API_KEY, "anthropic-version": "2023-06-01", "content-type": "application/json"},
                    json={"model": MODEL, "max_tokens": 8192, "messages": messages},
                    timeout=aiohttp.ClientTimeout(total=300)
                ) as resp:
                    if resp.status != 200:
                        return None
                    data = await resp.json()
                    content = data.get("content", [])
                    return content[0].get("text", "") if content else None
            except:
                return None

    async def _build(self, file_path):
        try:
            subprocess.run(["lake", "exe", "cache", "get"], cwd=str(HODGE_PATH), capture_output=True, timeout=300)
            result = subprocess.run(["lake", "build"], cwd=str(HODGE_PATH), capture_output=True, text=True, timeout=600)
            return result.returncode == 0, result.stdout + result.stderr
        except Exception as e:
            return False, str(e)

    async def _apply_code(self, task, resp, log):
        import re
        matches = re.findall(r"```lean\n(.*?)```", resp, re.DOTALL)
        if matches:
            path = HODGE_PATH / task.file_path
            path.parent.mkdir(parents=True, exist_ok=True)
            with open(path, "w") as f:
                f.write(max(matches, key=len))
            log(f"Wrote: {path}")

    async def run(self):
        print("=" * 60)
        print(f"MASSIVE PARALLEL COORDINATOR - {MAX_CONCURRENT_AGENTS} agents")
        print("=" * 60)
        self.load_state()
        if not ANTHROPIC_API_KEY:
            print("ERROR: Set ANTHROPIC_API_KEY")
            return

        active = []
        while True:
            active = [t for t in active if not t.done()]
            ready = self.get_ready()

            if not ready and not active:
                pending = [t for t in self.tasks.values() if t.status == TaskStatus.PENDING]
                if not pending:
                    print("\nALL DONE!")
                    break
                await asyncio.sleep(5)
                continue

            for task in ready[:MAX_CONCURRENT_AGENTS - len(active)]:
                print(f"Launching: {task.id}")
                active.append(asyncio.create_task(self.run_agent(task)))

            print(f"Active: {len(active)}, Done: {len(self.completed)}, Ready: {len(ready)}")
            await asyncio.sleep(2)


if __name__ == "__main__":
    import sys
    if len(sys.argv) > 1 and sys.argv[1] == "status":
        if STATE_FILE.exists():
            with open(STATE_FILE) as f:
                for t in json.load(f).get("tasks", []):
                    print(f"{t['status']:12} {t['id']}")
    else:
        asyncio.run(Coordinator().run())
