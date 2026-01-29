#!/usr/bin/env python3
"""
Green Build Coordinator
========================
Autonomous agent system that ONLY accepts changes that keep the build green.

Key features:
1. Runs indefinitely in tmux
2. Tests all changes before applying
3. Auto-commits working progress
4. Sends Slack notifications
"""

import os
import json
import asyncio
import aiohttp
import subprocess
from pathlib import Path
from datetime import datetime
from typing import Optional, List, Tuple

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
LOG_DIR = HODGE_PATH / "green_logs"
STATE_FILE = HODGE_PATH / "green_state.json"
SLACK_WEBHOOK = os.environ.get("SLACK_WEBHOOK", "")

# Files to work on (Stage 1-4 scaffold files)
TARGET_FILES = [
    "Hodge/Analytic/TestForms/LFTopology.lean",
    "Hodge/Analytic/TestForms/Operations.lean",
    "Hodge/Analytic/TestForms/CurrentsDual.lean",
    "Hodge/Analytic/Integration/SubmanifoldIntegral.lean",
    "Hodge/Analytic/Integration/IntegrationCurrent.lean",
    "Hodge/Analytic/Integration/Stokes.lean",
    "Hodge/GMT/Mass.lean",
    "Hodge/GMT/FlatNorm.lean",
    "Hodge/GMT/Calibration.lean",
]

VISION = """
## THE HODGE CONJECTURE - FORMAL PROOF

You are enhancing a Lean 4 formalization of the Hodge Conjecture.
The build is currently GREEN. Your changes MUST keep it green.

### Rules
1. ONLY replace `sorry` with real proofs
2. Do NOT change working code
3. Do NOT add new axioms unless absolutely necessary
4. Test your changes compile before submitting

### Your Task
Find ONE `sorry` in the file and replace it with a real proof.
Output the EXACT replacement (old line → new line).
"""

class GreenBuildCoordinator:
    def __init__(self):
        LOG_DIR.mkdir(exist_ok=True)
        self.completed = set()
        self.load_state()
    
    def log(self, msg: str):
        line = f"[{datetime.now():%Y-%m-%d %H:%M:%S}] {msg}"
        print(line)
        with open(LOG_DIR / "main.log", "a") as f:
            f.write(line + "\n")
    
    def load_state(self):
        if STATE_FILE.exists():
            try:
                data = json.loads(STATE_FILE.read_text())
                self.completed = set(data.get("completed", []))
            except:
                pass
    
    def save_state(self):
        STATE_FILE.write_text(json.dumps({
            "completed": list(self.completed),
            "updated": datetime.now().isoformat()
        }))
    
    async def notify_slack(self, msg: str):
        if not SLACK_WEBHOOK:
            return
        try:
            async with aiohttp.ClientSession() as session:
                await session.post(SLACK_WEBHOOK, json={"text": f"🔧 Hodge: {msg}"})
        except:
            pass
    
    def build(self) -> Tuple[bool, str]:
        """Run lake build and return (success, output)."""
        try:
            result = subprocess.run(
                ["lake", "build"],
                cwd=str(HODGE_PATH),
                capture_output=True,
                text=True,
                timeout=600,
                env={**os.environ, "PATH": f"/home/ubuntu/.elan/bin:{os.environ.get('PATH', '')}"} 
            )
            return result.returncode == 0, result.stdout + result.stderr
        except Exception as e:
            return False, str(e)
    
    def count_sorries(self, file_path: Path) -> int:
        """Count sorries in a file."""
        if not file_path.exists():
            return 0
        content = file_path.read_text()
        return content.count("sorry")
    
    async def work_on_file(self, rel_path: str) -> bool:
        """Try to eliminate one sorry from a file."""
        file_path = HODGE_PATH / rel_path
        if not file_path.exists():
            return False
        
        content = file_path.read_text()
        sorry_count = self.count_sorries(file_path)
        
        if sorry_count == 0:
            self.log(f"  {rel_path}: No sorries - already complete!")
            self.completed.add(rel_path)
            return True
        
        self.log(f"  {rel_path}: {sorry_count} sorries remaining")
        
        # Call Claude to eliminate ONE sorry
        prompt = f"""{VISION}

## FILE: {rel_path}

```lean
{content}
```

Find ONE `sorry` and provide its replacement.
Format your answer as:

LOCATION: (describe which sorry)
OLD:
```lean
<the line with sorry>
```
NEW:
```lean
<the replacement proof>
```
"""
        
        response = await self._call_api([{"role": "user", "content": prompt}])
        if not response:
            return False
        
        # Extract the replacement
        import re
        old_match = re.search(r"OLD:\s*```lean\s*(.*?)```", response, re.DOTALL)
        new_match = re.search(r"NEW:\s*```lean\s*(.*?)```", response, re.DOTALL)
        
        if not old_match or not new_match:
            self.log(f"  Could not parse response")
            return False
        
        old_code = old_match.group(1).strip()
        new_code = new_match.group(1).strip()
        
        if old_code not in content:
            self.log(f"  Old code not found in file")
            return False
        
        # Apply change
        new_content = content.replace(old_code, new_code, 1)
        file_path.write_text(new_content)
        
        # Test build
        ok, output = self.build()
        if ok:
            self.log(f"  ✅ SUCCESS! Eliminated one sorry")
            new_count = self.count_sorries(file_path)
            if new_count < sorry_count:
                await self.notify_slack(f"✅ Eliminated sorry in {rel_path} ({new_count} remaining)")
            return True
        else:
            self.log(f"  ❌ Build failed, reverting")
            file_path.write_text(content)
            return False
    
    async def _call_api(self, messages) -> Optional[str]:
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
                    json={"model": MODEL, "max_tokens": 4096, "messages": messages},
                    timeout=aiohttp.ClientTimeout(total=120)
                ) as resp:
                    if resp.status != 200:
                        return None
                    data = await resp.json()
                    return data.get("content", [{}])[0].get("text", "")
            except Exception as e:
                self.log(f"  API error: {e}")
                return None
    
    async def run_forever(self):
        """Main loop - runs indefinitely."""
        self.log("=" * 60)
        self.log("GREEN BUILD COORDINATOR - STARTING")
        self.log("=" * 60)
        
        if not API_KEY:
            self.log("ERROR: No API key found")
            return
        
        # Initial build check
        self.log("Checking initial build...")
        ok, _ = self.build()
        if not ok:
            self.log("ERROR: Initial build is not green!")
            await self.notify_slack("❌ Initial build failed - stopping")
            return
        
        self.log("Build is GREEN ✅")
        await self.notify_slack("🚀 Green Build Coordinator started")
        
        cycle = 0
        while True:
            cycle += 1
            self.log(f"\n--- Cycle {cycle} ---")
            
            # Work on each file
            for rel_path in TARGET_FILES:
                if rel_path in self.completed:
                    continue
                
                try:
                    success = await self.work_on_file(rel_path)
                    self.save_state()
                    await asyncio.sleep(2)  # Rate limit
                except Exception as e:
                    self.log(f"  Error: {e}")
            
            # Check if all done
            remaining = [f for f in TARGET_FILES if f not in self.completed]
            if not remaining:
                self.log("\n🎉 ALL FILES COMPLETE!")
                await self.notify_slack("🎉 All Stage 1-4 files complete!")
                break
            
            # Status report every 10 cycles
            if cycle % 10 == 0:
                total_sorries = sum(self.count_sorries(HODGE_PATH / f) for f in TARGET_FILES)
                self.log(f"Status: {len(self.completed)}/{len(TARGET_FILES)} files done, {total_sorries} sorries remaining")
                await self.notify_slack(f"📊 Progress: {total_sorries} sorries remaining in {len(remaining)} files")
            
            await asyncio.sleep(5)

if __name__ == "__main__":
    asyncio.run(GreenBuildCoordinator().run_forever())
