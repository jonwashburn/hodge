# Full-Unconditional (“No Gotchas”) Playbook

This is the **operational playbook** for completing the Lean formalization in this repo **mathematically** (not just kernel-clean).

It is written for:
- **Integrator (primary)**: coordinates semantic restoration, does cross-cutting changes, fixes breakage.
- **Agents (bounded workers)**: do **small, tightly-scoped** lemma/probing tasks only.

This document is intentionally strict because the repo can currently compile while still containing semantic stubs.

---

## Strong completion criterion (what “done” means)

We are done only when:
- **No `sorry`** in the proof-track code we care about.
- **No custom `axiom` or `opaque`** in `Hodge/`.
- **No semantic stubs** in the proof track:
  - no key maps/objects defined as `0`;
  - no key predicates defined as `True`;
  - no key geometric sets defined as `Set.univ`;
  - no “analytic/algebraic = closed” hacks;
  - no “cycle class = representing form” tautologies.
- `lake env lean Hodge/Utils/DependencyCheck.lean` reports only: `propext`, `Classical.choice`, `Quot.sound`.
- `./scripts/audit_practical_unconditional.sh` passes **unchanged**.

---

## Non-negotiable repo rules (build/audit)

**Before any `lake build`:**

```bash
lake exe cache get
```

**Preferred build:**

```bash
./scripts/build.sh
```

**Required checks (must stay unchanged):**

```bash
./scripts/audit_practical_unconditional.sh
./scripts/audit_stubs.sh --full
lake env lean Hodge/Utils/DependencyCheck.lean

grep -RIn --include="*.lean" -E '^[[:space:]]*sorry([^[:alnum:]_]|$)' Hodge/
grep -RIn --include="*.lean" -E '^[[:space:]]*axiom\\b' Hodge/
grep -RIn --include="*.lean" -E '^[[:space:]]*opaque\\b' Hodge/
```

**Important**:
- Do **not** “fix” audits by editing the audit scripts.
- Do **not** hide gotchas by moving files to quarantine/off-track.

---

## Role split

### Integrator responsibilities (cross-cutting / high risk)

Only the integrator should do these because they touch many files and are easy to “solve” incorrectly:
- Restore real meanings for:
  - `SignedAlgebraicCycle.cycleClass_geom`;
  - `FundamentalClassSet` / Poincaré duality;
  - `SubmanifoldIntegration`;
  - analytic vs algebraic notions;
  - SYR microstructure sequence (non-constant, real sheets + gluing + defect → 0);
  - Harvey–Lawson/King output (real analytic varieties);
  - Chow/GAGA (analytic→algebraic on projective manifolds).
- Remove `.universal` / trivial instances from the actual proof spine.
- Keep everything compiling and keep audits green after each semantic step.

### Agent responsibilities (bounded / low risk)

Agents may only do one of:
- **Lemma packages**: 1–3 lemmas, 1–2 files, no semantic definitions changes.
- **Repo archaeology**: locate exact call sites / dependencies, produce a written report in `docs/`.
- **Micro-infrastructure**: small general-purpose lemmas needed by integrator refactors.

Agents must not touch:
- theorem statements on the proof track (no weakening);
- definitions of key notions (analytic/algebraic/integration/cycle class);
- audit scripts.

---

## Forbidden “gotcha” patterns (agents and integrator)

Do **not**:
- introduce any `axiom` / `opaque` / `sorry`;
- “prove” deep statements by changing definitions to `0`, `True`, `Set.univ`, etc.;
- redefine:
  - `IsAnalyticSet := IsClosed`,
  - `IsAlgebraicSet := IsClosed`,
  - `cycleClass_geom := cycleClass`,
  - `FundamentalClassSet := ω^p` or any other fixed placeholder;
- delete/move pillars to quarantine to bypass dependencies.

Allowed axioms in final dependency output: `propext`, `Classical.choice`, `Quot.sound` only.

---

## Patch discipline (agent checklist)

Every agent patch must include (in the agent’s final message / PR description):
- **What changed**:
  - files touched;
  - lemma names added/edited;
  - short explanation of proof idea.
- **What did NOT change**:
  - no theorem statement weakening;
  - no definition changes to semantic objects.
- **Commands run** (must include):

```bash
./scripts/build.sh
./scripts/audit_practical_unconditional.sh
./scripts/audit_stubs.sh --full
lake env lean Hodge/Utils/DependencyCheck.lean
```

If you ran `lake env lean Some/File.lean`, you must also run `./scripts/build.sh` (because `lake env lean` does not build missing `.olean` dependencies).

---

## “Safe to parallelize now” agent tasks (3–5 concrete specs)

These are designed to be **useful** for the TeX spine work you’re currently reading (template tails / transport-to-flat control) without touching semantic definitions.

### AG-01 — Relate recursion-based `finSum` to standard `Finset` sums

- **Files**: `Hodge/Analytic/FlatNorm.lean`
- **Goal**: Add conversion lemmas so future work can use `Finset.sum` APIs.
- **Targets** (all in `namespace Hodge.FlatNormFinite`):
  - `finSum_eq_sum_univ`:
    - statement: `finSum N T = ∑ i : Fin N, T i`
  - `finSumℝ_eq_sum_univ`:
    - statement: `finSumℝ N cost = ∑ i : Fin N, cost i`
- **Constraints**:
  - do not change definitions of `finSum` / `finSumℝ`;
  - no new stubs.

### AG-02 — General `Finset` triangle inequality for `flatNorm`

- **Files**: `Hodge/Analytic/FlatNorm.lean`
- **Goal**: Provide a reusable lemma:
  - `flatNorm_sum_le_sum_flatNorm`:
    - statement: `flatNorm (∑ i in s, T i) ≤ ∑ i in s, flatNorm (T i)`
- **Notes**:
  - This should be a clean induction on `Finset`.
  - Avoid fragile `simp` loops; prefer explicit `Finset.induction_on` + `flatNorm_add_le`.

### AG-03 — Combinatorial “unmatched tail” variants

- **Files**: `Hodge/GMT/TemplateExtension.lean`
- **Goal**: Add 1–2 helper lemmas rewriting the “tail” finsets into standard intervals (if available in Mathlib),
  so later microstructure code can read closer to TeX.
- **Targets** (example style; pick whichever is available/easy in this Mathlib snapshot):
  - `range_sdiff_range_eq_Icc` or similar;
  - a lemma that turns the tail sum into a sum over an interval.
- **Constraints**: no changes to existing lemmas; only additive helpers.

### AG-04 — (Docs) Exact map of semantic gotchas on the proof spine

- **Files**: add `docs/SEMANTIC_GOTCHAS_INDEX.md` (new)
- **Goal**: produce a “clickable” index of the remaining **semantic** blockers, with file+line references:
  - `cycleClass_geom` alias location(s);
  - `Chow/GAGA` closedness approximations;
  - `SubmanifoldIntegration.universal` and any other `:= 0` integration stubs;
  - `microstructureSequence_real := zero_int` location;
  - any remaining `True`-based placeholders that are still on the proof spine.

### AG-05 — (Docs) Minimal Mathlib leverage survey for analytic/algebraic geometry

- **Files**: add `docs/MATHLIB_LEVERAGE_GAGA_CHOW.md` (new)
- **Goal**: identify what (if anything) exists in bundled Mathlib for:
  - complex analytic sets / holomorphic functions / local zero loci;
  - projective varieties / schemes;
  - any existing “Chow theorem”/GAGA statements.
- **Deliverable**: a short report with module paths (if they exist) and what’s missing.

---

## Integrator next-step checklist (semantic restoration order)

When the integrator starts the next phase, the safest dependency order is:
1. Replace `cycleClass_geom` alias with the **support/fundamental-class definition**, keep compilation by updating bridge lemmas.
2. Replace “analytic/algebraic = closed” with real definitions (even if proofs are initially missing, do **not** replace them with `True`).
3. Replace `SubmanifoldIntegration.universal` and `SubmanifoldIntegration.real` (currently still zero-integral) with genuine integration theory.
4. Replace `microstructureSequence_real := zero_int` with an actual sheet/gluing construction and prove defect→0 using the GMT spine lemmas.

The integrator must keep all audits green after each step.

