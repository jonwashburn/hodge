#!/usr/bin/env python3
"""
Initialize a deep-coordinator task batch for removing major semantic stub *instances*
while keeping the repo compiling (no `sorry`).
"""

from __future__ import annotations

import json
from datetime import datetime
from pathlib import Path


HODGE_PATH = Path("/home/ubuntu/hodge")
STATE_FILE = HODGE_PATH / "deep_agent_state.json"


def task(
    *,
    id: str,
    description: str,
    file_path: str,
    target: str,
    dependencies: list[str] | None = None,
) -> dict:
    return {
        "id": id,
        "description": description,
        "file_path": file_path,
        "target": target,
        "status": "pending",
        "dependencies": dependencies or [],
        "iterations": 0,
        "result": None,
        "error": None,
    }


def main() -> None:
    tasks = [
        task(
            id="stub_remove_submanifoldintegration_instance",
            description="Remove the stubbed `SubmanifoldIntegration.universal` instance (currently `integral := 0`) and make its dependency explicit where needed.",
            file_path="Hodge/Analytic/Integration/HausdorffMeasure.lean",
            target="Delete `SubmanifoldIntegration.universal` and ensure module compiles (no new sorries/axioms).",
        ),
        task(
            id="stub_propagate_submanifoldintegration_currents",
            description="Propagate `[SubmanifoldIntegration n X]` explicitly through `setIntegral` plumbing so we no longer rely on a global instance.",
            file_path="Hodge/Analytic/Currents.lean",
            target="Update `setIntegral`/`setIntegral_*` signatures and call sites to work without `SubmanifoldIntegration.universal`.",
            dependencies=["stub_remove_submanifoldintegration_instance"],
        ),
        task(
            id="stub_fix_microstructure_after_submanifoldintegration",
            description="Remove all `SubmanifoldIntegration.universal` references and false 'integral=0' reasoning in Microstructure; use explicit Stokes/integrality interfaces instead.",
            file_path="Hodge/Kahler/Microstructure.lean",
            target="Update `RawSheetSum.toIntegrationData` stokes proof, `RawSheetSum.toCycleIntegralCurrent`, and drop `RawSheetSumZeroBound.universal` (no stubbed reasoning).",
            dependencies=[
                "stub_remove_submanifoldintegration_instance",
                "stub_propagate_submanifoldintegration_currents",
            ],
        ),
        task(
            id="stub_remove_poincaredualform_universal",
            description="Remove `CycleClass.PoincareDualFormExists.universal` (currently chooses `{ form := 0, ... }`).",
            file_path="Hodge/Classical/CycleClass.lean",
            target="Delete the universal instance; ensure the module compiles with explicit `[PoincareDualFormExists ...]` assumptions only.",
        ),
        task(
            id="validate_after_stub_removal",
            description="Validate the repo still builds and main theorems remain kernel-axiom clean after stub-instance removal.",
            file_path="Hodge/Kahler/Main.lean",
            target="Run `lake build` and `#print axioms hodge_conjecture'`/`hodge_conjecture`.",
            dependencies=[
                "stub_fix_microstructure_after_submanifoldintegration",
                "stub_remove_poincaredualform_universal",
            ],
        ),
    ]

    state = {
        "tasks": {t["id"]: t for t in tasks},
        "updated": datetime.now().isoformat(),
    }
    STATE_FILE.write_text(json.dumps(state, indent=2) + "\n")
    print(f"Wrote {STATE_FILE} with {len(tasks)} tasks.")


if __name__ == "__main__":
    main()

