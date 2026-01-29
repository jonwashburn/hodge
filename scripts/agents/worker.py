#!/usr/bin/env python3
"""
Hodge Agent Worker - A Claude instance that can read/write files and run Lean
=============================================================================
This worker receives tasks from the coordinator and has full filesystem access.
"""

import os
import json
import subprocess
import aiohttp
from pathlib import Path
from dataclasses import dataclass
from typing import Optional, List, Dict, Any
import re
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
MODEL = "claude-opus-4-5-20251101"
HODGE_PATH = Path(os.environ.get("HODGE_PATH", "/home/ubuntu/hodge"))


@dataclass
class ToolResult:
    success: bool
    output: str


class LeanWorker:
    """A worker that can interact with the Lean codebase."""
    
    def __init__(self, session: aiohttp.ClientSession):
        self.session = session
        self.conversation: List[Dict] = []
        # Allow longer runs for research-heavy tasks (docs surveys, large refactors).
        # Can be overridden per-run: `MAX_ITERATIONS=30 python3 worker.py ...`
        try:
            self.max_iterations = int(os.environ.get("MAX_ITERATIONS", "25"))
        except Exception:
            self.max_iterations = 25
        # Ensure we never rebuild Mathlib from source on the server: run `lake exe cache get` once.
        # (Repo rule: ALWAYS fetch cache before any `lake build`.)
        self._mathlib_cache_ready_flag = HODGE_PATH / ".mathlib_cache_ready"

    def _ensure_mathlib_cache(self) -> ToolResult:
        """Run `lake exe cache get` once per repo clone to avoid rebuilding Mathlib from source."""
        try:
            if self._mathlib_cache_ready_flag.exists():
                return ToolResult(True, "Mathlib cache already fetched")
            result = subprocess.run(
                ["lake", "exe", "cache", "get"],
                cwd=HODGE_PATH,
                capture_output=True,
                text=True,
                timeout=900,
            )
            output = (result.stdout or "") + (result.stderr or "")
            if result.returncode != 0:
                return ToolResult(False, "Mathlib cache fetch failed:\n" + output[-4000:])
            try:
                self._mathlib_cache_ready_flag.write_text("ok\n")
            except Exception:
                # Non-fatal: cache fetch succeeded; flag is just an optimization.
                pass
            return ToolResult(True, "Mathlib cache fetched:\n" + output[-4000:])
        except subprocess.TimeoutExpired:
            return ToolResult(False, "Mathlib cache fetch timed out")
        except Exception as e:
            return ToolResult(False, f"Error while fetching Mathlib cache: {e}\n{traceback.format_exc()}")

    async def call_claude(
        self,
        messages: List[Dict],
        system: str,
        tools: List[Dict] = None
    ) -> Dict:
        """Call Claude API with tools."""
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
        }
        if tools:
            payload["tools"] = tools
        
        async with self.session.post(
            "https://api.anthropic.com/v1/messages",
            headers=headers,
            json=payload
        ) as resp:
            if resp.status != 200:
                error_text = await resp.text()
                raise Exception(f"API error {resp.status}: {error_text}")
            return await resp.json()

    def execute_tool(self, name: str, input_data: Dict) -> ToolResult:
        """Execute a tool call."""
        try:
            if name == "read_file":
                path = HODGE_PATH / input_data["path"]
                if path.exists():
                    content = path.read_text()
                    return ToolResult(True, content)
                return ToolResult(False, f"File not found: {path}")
            
            elif name == "write_file":
                path = HODGE_PATH / input_data["path"]
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(input_data["content"])
                return ToolResult(True, f"Wrote {len(input_data['content'])} chars to {path}")
            
            elif name == "search_replace":
                path = HODGE_PATH / input_data["path"]
                if not path.exists():
                    return ToolResult(False, f"File not found: {path}")
                content = path.read_text()
                old = input_data["old_string"]
                new = input_data["new_string"]
                if old not in content:
                    return ToolResult(False, f"String not found in file: {old[:100]}...")
                new_content = content.replace(old, new, 1)
                path.write_text(new_content)
                return ToolResult(True, "Replacement successful")
            
            elif name == "run_lake_build":
                target = input_data.get("target", "")
                cache_res = self._ensure_mathlib_cache()
                if not cache_res.success:
                    return cache_res
                cmd = ["lake", "build"]
                if target:
                    cmd.append(target)
                result = subprocess.run(
                    cmd,
                    cwd=HODGE_PATH,
                    capture_output=True,
                    text=True,
                    timeout=300
                )
                output = result.stdout + result.stderr
                return ToolResult(result.returncode == 0, output[-4000:])  # Truncate
            
            elif name == "run_lake_check":
                target = input_data.get("file", "")
                cache_res = self._ensure_mathlib_cache()
                if not cache_res.success:
                    return cache_res
                cmd = ["lake", "env", "lean", target]
                result = subprocess.run(
                    cmd,
                    cwd=HODGE_PATH,
                    capture_output=True,
                    text=True,
                    timeout=120
                )
                output = result.stdout + result.stderr
                return ToolResult(result.returncode == 0, output[-4000:])
            
            elif name == "grep":
                pattern = input_data["pattern"]
                path = input_data.get("path", ".")
                cmd = ["grep", "-rn", "--include=*.lean", pattern, str(HODGE_PATH / path)]
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
                return ToolResult(True, result.stdout[-4000:] or "No matches")
            
            elif name == "list_dir":
                path = HODGE_PATH / input_data.get("path", ".")
                if not path.exists():
                    return ToolResult(False, f"Directory not found: {path}")
                items = sorted(path.iterdir())
                listing = "\n".join(
                    f"{'[dir] ' if i.is_dir() else ''}{i.name}"
                    for i in items
                )
                return ToolResult(True, listing)
            
            elif name == "print_axioms":
                theorem = input_data["theorem"]
                # Create temp file to check axioms
                check_code = f"""
import Hodge

#print axioms {theorem}
"""
                check_file = HODGE_PATH / "_check_axioms.lean"
                check_file.write_text(check_code)
                result = subprocess.run(
                    ["lake", "env", "lean", str(check_file)],
                    cwd=HODGE_PATH,
                    capture_output=True,
                    text=True,
                    timeout=120
                )
                check_file.unlink(missing_ok=True)
                return ToolResult(True, result.stdout + result.stderr)
            
            elif name == "complete":
                return ToolResult(True, f"Task completed: {input_data.get('summary', 'done')}")
            
            else:
                return ToolResult(False, f"Unknown tool: {name}")
                
        except subprocess.TimeoutExpired:
            return ToolResult(False, "Command timed out")
        except Exception as e:
            return ToolResult(False, f"Error: {str(e)}\n{traceback.format_exc()}")

    async def work_on_task(self, task_description: str, file_path: str, target: str) -> Dict:
        """Have the worker complete a task using tools."""
        
        tools = [
            {
                "name": "read_file",
                "description": "Read a file from the Hodge repository",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "path": {"type": "string", "description": "Path relative to repo root"}
                    },
                    "required": ["path"]
                }
            },
            {
                "name": "write_file",
                "description": "Write content to a file",
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
                "description": "Replace a string in a file",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "path": {"type": "string"},
                        "old_string": {"type": "string"},
                        "new_string": {"type": "string"}
                    },
                    "required": ["path", "old_string", "new_string"]
                }
            },
            {
                "name": "run_lake_build",
                "description": "Run lake build to compile the project",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "target": {"type": "string", "description": "Optional module to build"}
                    }
                }
            },
            {
                "name": "run_lake_check",
                "description": "Check a single Lean file for errors",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "file": {"type": "string", "description": "Path to .lean file"}
                    },
                    "required": ["file"]
                }
            },
            {
                "name": "grep",
                "description": "Search for a pattern in .lean files",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "pattern": {"type": "string"},
                        "path": {"type": "string", "description": "Subdirectory to search"}
                    },
                    "required": ["pattern"]
                }
            },
            {
                "name": "list_dir",
                "description": "List contents of a directory",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "path": {"type": "string"}
                    }
                }
            },
            {
                "name": "print_axioms",
                "description": "Print axioms used by a theorem",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "theorem": {"type": "string", "description": "Fully qualified theorem name"}
                    },
                    "required": ["theorem"]
                }
            },
            {
                "name": "complete",
                "description": "Mark the task as complete with a summary",
                "input_schema": {
                    "type": "object",
                    "properties": {
                        "summary": {"type": "string"},
                        "success": {"type": "boolean"},
                        "changes_made": {"type": "string"}
                    },
                    "required": ["summary", "success"]
                }
            }
        ]
        
        system = f"""You are an expert Lean 4 mathematician working on the Hodge Conjecture formalization.

GOAL: Eliminate the sorry or axiom at {target} in {file_path}

WORKFLOW:
1. Read the target file and understand the context
2. Search for relevant Mathlib lemmas using grep
3. Write a proper proof replacing the sorry
4. Run lake check to verify it compiles
5. If there are errors, fix them iteratively
6. When done, call complete with a summary

RULES:
- Use Mathlib 4 conventions
- Only modify what's necessary
- If the proof requires deep mathematical content you can't formalize, 
  document what's needed and mark as incomplete
- Maximum {self.max_iterations} tool calls

Current task: {task_description}
"""

        messages = [{
            "role": "user",
            "content": f"Please work on: {task_description}\n\nTarget: {target} in {file_path}\n\nStart by reading the file."
        }]
        
        for i in range(self.max_iterations):
            response = await self.call_claude(messages, system, tools)
            
            # Check stop reason
            if response.get("stop_reason") == "end_turn":
                # No tool use, model is done
                content = response["content"]
                text = next((c["text"] for c in content if c["type"] == "text"), "")
                return {"success": False, "output": text, "iterations": i}
            
            # Process tool calls
            content = response["content"]
            tool_uses = [c for c in content if c["type"] == "tool_use"]
            
            if not tool_uses:
                text = next((c["text"] for c in content if c["type"] == "text"), "")
                return {"success": False, "output": text, "iterations": i}
            
            # Add assistant message
            messages.append({"role": "assistant", "content": content})
            
            # Execute tools and collect results
            tool_results = []
            complete_result = None
            
            for tool_use in tool_uses:
                result = self.execute_tool(tool_use["name"], tool_use["input"])
                tool_results.append({
                    "type": "tool_result",
                    "tool_use_id": tool_use["id"],
                    "content": result.output
                })
                
                if tool_use["name"] == "complete":
                    complete_result = tool_use["input"]
            
            messages.append({"role": "user", "content": tool_results})
            
            if complete_result:
                return {
                    "success": complete_result.get("success", False),
                    "output": complete_result.get("summary", ""),
                    "changes": complete_result.get("changes_made", ""),
                    "iterations": i + 1
                }
        
        return {"success": False, "output": "Max iterations reached", "iterations": self.max_iterations}


async def main():
    """Test the worker on a sample task."""
    import sys
    
    if len(sys.argv) < 2:
        print("Usage: python worker.py <task_description>")
        print("Example: python worker.py 'Prove zero_hasStokesProperty in Hodge/Analytic/Currents.lean'")
        return
    
    task = sys.argv[1]
    file_path = sys.argv[2] if len(sys.argv) > 2 else "Hodge/Analytic/Currents.lean"
    target = sys.argv[3] if len(sys.argv) > 3 else "zero_hasStokesProperty"
    
    async with aiohttp.ClientSession() as session:
        worker = LeanWorker(session)
        result = await worker.work_on_task(task, file_path, target)
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    import asyncio
    asyncio.run(main())
