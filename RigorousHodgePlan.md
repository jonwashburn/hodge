# Rigorous Formalization Plan: Hodge Conjecture

**Goal:** Machine-verified proof with **zero** `sorry`, `admit`, or `axiom` statements.

**Current Status:** 94 sorries + 5 True placeholders across 18 files ⚠️

---

## 🚨🚨🚨 STOP! READ YOUR TRACK ASSIGNMENT FIRST 🚨🚨🚨

**YOU MAY ONLY EDIT THE FILES ASSIGNED TO YOUR TRACK. NO EXCEPTIONS.**

| If you are... | You may ONLY edit these files | DO NOT TOUCH |
|---------------|------------------------------|--------------|
| **Track A1** | `Classical/SerreVanishing.lean` | Everything else |
| **Track A2** | `Classical/Bergman.lean` | Everything else |
| **Track A3** | `Classical/GAGA.lean`, `Classical/FedererFleming.lean` | Everything else |
| **Track A4** | `Analytic/Calibration.lean`, `Analytic/Norms.lean`, `Analytic/Grassmannian.lean` | Everything else |
| **Track A5** | `Kahler/Cone.lean`, `Kahler/Microstructure.lean`, `Kahler/TypeDecomposition.lean` | Everything else |

### ❌ IF YOU SEE AN ERROR IN ANOTHER FILE:
- **DO NOT FIX IT** — that's another agent's job
- **DO NOT EDIT IT** — you will create merge conflicts
- **ONLY WORK ON YOUR ASSIGNED FILES**

### ❌ THESE FILES ARE OFF-LIMITS TO EVERYONE:
`Basic.lean`, `Main.lean`, `Kahler/Main.lean`, `HarveyLawson.lean`, `Lefschetz.lean`, `IntegralCurrents.lean`, `Forms.lean`, `Currents.lean`, `FlatNorm.lean`, `Manifolds.lean`, `SignedDecomp.lean`

---

## ⚠️ PROOF QUALITY STANDARDS

**This is a quality proof, not a checkbox exercise.** Every definition and theorem must be mathematically meaningful.

### Absolutely Forbidden:
- ❌ **Vacuous definitions** like `def X := sorry` or `def X : Type* := Unit`
- ❌ **Trivial propositions** like `theorem foo : True := trivial`
- ❌ **Placeholder fields** like `is_something : Prop := True`
- ❌ **Empty structures** that compile but prove nothing
- ❌ **Circular reasoning** or assuming what you're trying to prove
- ❌ **Rushing to remove `sorry`** without understanding the mathematics

### Required:
- ✅ **Every definition must have mathematical content** — if you define `SheafCohomology`, it must actually be sheaf cohomology (derived functors), not a placeholder type
- ✅ **Every theorem must have a real proof** — the proof term must actually establish the statement, not just make Lean happy
- ✅ **Consult references** — these are deep theorems (Harvey-Lawson, GAGA, Federer-Fleming); read the cited papers if needed
- ✅ **Ask for help** if a proof is beyond current Mathlib — it's better to document a genuine gap than fake a proof
- ✅ **Preserve mathematical intent** — the LaTeX manuscript `Hodge-v6-w-Jon-Update-MERGED.tex` contains the intended arguments

### Quality Check:
Before claiming a `sorry` is resolved, ask yourself:
1. Does this definition/proof actually mean what the docstring says?
2. Would a mathematician reading this accept it as rigorous?
3. Is there any way this could be vacuously true or trivially satisfied?

---

## 🚀 AGENT TRACKS (5 Parallel Agents)

Each agent works on isolated files to minimize build conflicts. Just prompt:
> "Work on @RigorousHodgePlan.md Track A1"

---

### Track A1: Serre Vanishing (13 sorries + 1 True placeholder) ⚠️ NEEDS QUALITY FIX

**File:** `Hodge/Classical/SerreVanishing.lean`

**Build command:** `lake build Hodge.Classical.SerreVanishing`

**⚠️ QUALITY ISSUES TO FIX:**

| Line | Issue | What's Wrong |
|------|-------|--------------|
| 35 | `sorry` in `holomorphicSheaf.map` | MDifferentiable composition not proved |
| 39 | `sorry` in `holomorphicSheaf.cond` | Sheaf condition not proved |
| 50 | `True` placeholder | `is_locally_presented` returns trivial `True` — **FORBIDDEN** |
| 56 | `sorry` in `structureSheaf.sheaf` | No actual sheaf construction |
| 57 | `sorry` in `structureSheaf.is_locally_presented` | No presentation proof |
| 63-64 | `sorry` in `tensorWithSheaf` | Both fields are sorry |
| 68-69 | `sorry` in `idealSheaf` | Both fields are sorry |
| 73-74 | `sorry` in `jetSkyscraperSheaf` | Both fields are sorry |
| 80 | `sorry` in `SheafCohomology` | Definition is literally `sorry` — **VACUOUS** |
| 98 | `sorry` in `serre_vanishing` | Theorem not proved |
| 120 | `sorry` in `jet_surjectivity_from_serre` | Theorem not proved |

**What needs to happen:**
1. **Remove the `True` placeholder** on line 50 — replace with actual presentation data
2. **Define `SheafCohomology` properly** — use Mathlib's `Sheaf.H` or derived functors
3. **Build real sheaf constructions** for `structureSheaf`, `tensorWithSheaf`, `idealSheaf`, `jetSkyscraperSheaf`
4. **Prove the theorems** or document genuine Mathlib gaps

**YOUR FILE:** `Classical/SerreVanishing.lean` — ONLY edit this file
**DO NOT EDIT:** Everything else, especially `Bergman.lean`, `GAGA.lean`, `FedererFleming.lean`

---

### Track A2: Bergman Kernels (15 sorries + 1 True placeholder) ⚠️ NEEDS QUALITY FIX

**File:** `Hodge/Classical/Bergman.lean`

**Build command:** `lake build Hodge.Classical.Bergman`

**Sorries to resolve:**
- `def HolomorphicLineBundle.tensor` — tensor product holomorphicity
- `def FirstChernClass` — first Chern class construction
- `def HolomorphicSection.tensor` — section tensor product
- `def BergmanMetric` — (i/2π) ∂∂̄ log K_M
- `theorem tian_convergence` — Bergman → Kähler in C^2
- `theorem jet_surjectivity` — jets are surjective for large M

**⚠️ Check for True placeholders and vacuous definitions**

**YOUR FILE:** `Classical/Bergman.lean` — ONLY edit this file
**DO NOT EDIT:** Everything else, especially `SerreVanishing.lean`, `GAGA.lean`, `FedererFleming.lean`

---

### Track A3: GAGA + Federer-Fleming (9 sorries)

**Files:** 
- `Hodge/Classical/GAGA.lean` (7 sorries)
- `Hodge/Classical/FedererFleming.lean` (2 sorries)

**Build commands:**
```bash
lake build Hodge.Classical.GAGA
lake build Hodge.Classical.FedererFleming
```

**GAGA sorries:**
- `theorem isAlgebraicSubvariety_union` — union of algebraic is algebraic
- `def FundamentalClass` — fundamental class in cohomology
- `theorem FundamentalClass_union` — additivity
- `theorem isAlgebraicSubvariety_intersection` — intersection
- `theorem serre_gaga` — analytic → algebraic on projective

**Federer-Fleming sorries:**
- `theorem deformation_theorem` — polyhedral approximation
- `theorem federer_fleming_compactness` — diagonal argument + completeness

**YOUR FILES:** `Classical/GAGA.lean`, `Classical/FedererFleming.lean` — ONLY edit these files
**DO NOT EDIT:** Everything else, especially `SerreVanishing.lean`, `Bergman.lean`, `HarveyLawson.lean`

---

### Track A4: Analytic Core (25 sorries)

**Files:**
- `Hodge/Analytic/Norms.lean` (15 sorries)
- `Hodge/Analytic/Calibration.lean` (6 sorries)
- `Hodge/Analytic/Grassmannian.lean` (4 sorries)

**Build commands:**
```bash
lake build Hodge.Analytic.Calibration
lake build Hodge.Analytic.Norms
lake build Hodge.Analytic.Grassmannian
```

**Calibration sorries:**
- `def KählerCalibration` — prove ω^p/p! is closed with comass ≤ 1

**Norms sorries:**
- `theorem pointwiseComass_continuous` — Berge maximum theorem
- `def kahlerMetricDual` — dual metric on cotangent
- `def pointwiseInner` — inner product of forms

**Grassmannian sorries:**
- `def simpleCalibratedForm` — volume form of complex p-plane
- `theorem calibratedCone_is_closed` — cone closure
- `theorem radial_minimization` — projection onto ray

**YOUR FILES:** `Analytic/Calibration.lean`, `Analytic/Norms.lean`, `Analytic/Grassmannian.lean` — ONLY edit these files
**DO NOT EDIT:** Everything else, especially `IntegralCurrents.lean`, `Forms.lean`, `Currents.lean`, any `Classical/` or `Kahler/` file

---

### Track A5: Kähler Geometry (8 sorries + 2 True placeholders)

**Files:**
- `Hodge/Kahler/Cone.lean` (4 sorries)
- `Hodge/Kahler/Microstructure.lean` (3 sorries)
- `Hodge/Kahler/TypeDecomposition.lean` (1 sorry + 2 True placeholders)

**Build commands:**
```bash
lake build Hodge.Kahler.Cone
lake build Hodge.Kahler.Microstructure
lake build Hodge.Kahler.TypeDecomposition
```

**Cone sorries:**
- `theorem wirtinger_pairing` — ⟨ω^p, ξ⟩ = 1 on complex planes
- `theorem ConvexCone.mem_interior_of_pairing_pos` — dual cone criterion
- `theorem omegaPow_in_interior` — ω^p in interior of K_p
- `theorem exists_uniform_interior_radius` — compactness argument
- `theorem caratheodory_decomposition` — finite convex combination

**Microstructure sorries:**
- `theorem local_sheet_realization` — jet surjectivity → sheets
- `theorem integer_transport` — total unimodularity
- `theorem gluing_estimate` — boundary flat norm bound

**TypeDecomposition sorries:**
- `theorem hodge_decomposition` — spectral projections

**YOUR FILES:** `Kahler/Cone.lean`, `Kahler/Microstructure.lean`, `Kahler/TypeDecomposition.lean` — ONLY edit these files
**DO NOT EDIT:** Everything else, especially `Kahler/Main.lean`, `Kahler/Manifolds.lean`, `Kahler/SignedDecomp.lean`, any `Classical/` or `Analytic/` file

---

## 🔒 PHASE 2 (After Tracks A1-A5 Complete)

These files have heavy dependencies — only work on them after above tracks are done:

| File | Sorries | Reason to defer |
|------|---------|-----------------|
| `Basic.lean` | 3 | Imported everywhere — edits cause full rebuild |
| `Kahler/Main.lean` | 8 | Imports all of Kahler/ and Classical/ |
| `Main.lean` | 5 | Final assembly — imports everything |
| `Classical/HarveyLawson.lean` | 3 | Imports Analytic/ |
| `Classical/Lefschetz.lean` | 2 | Imports Kahler/ |

---

## 📋 BUILD POLICY

1. **Never run `lake build` without arguments** — it rebuilds everything
2. **Use specific module builds:** `lake build Hodge.Classical.GAGA`
3. **Commit frequently, push at session end**
4. **If build fails on imports:** another agent may have broken something — coordinate

---

## 🎯 Milestone Targets

- **M1:** ✅ Structural Assembly Complete
- **M2:** Tracks A1-A5 complete (56 sorries → 0)
- **M3:** Phase 2 complete (21 sorries → 0)
- **M4:** Verified State — **zero** `sorry`, `axiom`, `admit`

---

*Last updated: 2024-12-26*
