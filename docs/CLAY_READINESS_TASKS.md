# Clay-readiness tasks (beyond kernel-axiom-clean)

This document tracks **what remains after** the proof-track kernel report is clean:

```
'hodge_conjecture'' depends on axioms: [propext, Classical.choice, Quot.sound]
```

When that happens, the project will be **Lean-kernel checked** and **sorry-free** (in the proof track),
but it may still be far from a **mathematically faithful Clay-grade formalization** due to
intentional *semantic stubs* / placeholder definitions.

---

## High-priority semantic stubs to replace (proof-track relevant)

### Currents / integration / Stokes
- **`Hodge/Analytic/Currents.lean`**
  - `integration_current` is currently a stub (`0`).
  - Goal: define real integration currents and prove the needed boundedness/Stokes properties.

### Microstructure analytic pairing
- **`Hodge/Kahler/Microstructure.lean`**
  - `SmoothForm.pairing` is currently a stub (`0`).
  - Goal: implement the actual pairing used in the TeX argument and prove its properties.

### Harvey–Lawson calibrated currents
- **`Hodge/Classical/HarveyLawson.lean`**
  - `harvey_lawson_theorem` is currently a semantic stub (returns empty varieties and `represents := True`).
  - Goal: formalize the genuine Harvey–Lawson structure theorem (major GMT/regularity project).

### Inner products / L² / analytic Hodge theory
- **`Hodge/Analytic/Norms.lean`**
  - Several inner-product/L² objects are stubbed as `0`.
  - Goal: implement real metric/Hodge-theoretic norms and operators as needed.

---

## Recommended workflow once Agent 1 finishes the last sorries

1. Run `./scripts/verify_proof_track.sh` and confirm the kernel report is clean.
2. Run `./scripts/audit_stubs.sh --full` and record the remaining placeholders.
3. Replace placeholders **one module at a time**, keeping `lake build Hodge.Kahler.Main` green.

