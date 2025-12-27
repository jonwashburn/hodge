# Rigorous Formalization Plan: Hodge Conjecture

**Goal:** Machine-verified proof with **zero** `sorry`, `admit`, or `axiom` statements.

**Current Status:** 77 sorries across 14 files

---

## 🚀 AGENT TRACKS (5 Parallel Agents)

Each agent works on isolated files to minimize build conflicts. Just prompt:
> "Work on @RigorousHodgePlan.md Track A1"

---

### Track A1: Serre Vanishing (14 sorries)

**File:** `Hodge/Classical/SerreVanishing.lean`

**Build command:** `lake build Hodge.Classical.SerreVanishing`

**Sorries to resolve:**
- `def SheafCohomology` — define via derived functors
- `theorem serre_vanishing` — prove H^q vanishes for large M
- `def tensorWithSheaf` — tensor product of line bundle with coherent sheaf
- `def idealSheaf` — sheaf of functions vanishing at x to order k
- `def jetSkyscraperSheaf` — skyscraper sheaf of jets
- `def structureSheaf` — cokernel presentation
- `theorem jet_surjectivity_from_serre` — derive from vanishing + LES

**DO NOT EDIT:** `Basic.lean`, `Main.lean`, any file outside `Classical/`

---

### Track A2: Bergman Kernels (12 sorries)

**File:** `Hodge/Classical/Bergman.lean`

**Build command:** `lake build Hodge.Classical.Bergman`

**Sorries to resolve:**
- `def HolomorphicLineBundle.tensor` — tensor product holomorphicity
- `def FirstChernClass` — first Chern class construction
- `def HolomorphicSection.tensor` — section tensor product
- `def BergmanMetric` — (i/2π) ∂∂̄ log K_M
- `theorem tian_convergence` — Bergman → Kähler in C^2
- `theorem jet_surjectivity` — jets are surjective for large M

**DO NOT EDIT:** `Basic.lean`, `Main.lean`, any file outside `Classical/`

---

### Track A3: GAGA + Federer-Fleming (11 sorries)

**Files:** 
- `Hodge/Classical/GAGA.lean` (7 sorries)
- `Hodge/Classical/FedererFleming.lean` (4 sorries)

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

**DO NOT EDIT:** `Basic.lean`, `Main.lean`, `HarveyLawson.lean`

---

### Track A4: Analytic Core (10 sorries)

**Files:**
- `Hodge/Analytic/Calibration.lean` (4 sorries)
- `Hodge/Analytic/Norms.lean` (3 sorries)
- `Hodge/Analytic/Grassmannian.lean` (3 sorries)

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

**DO NOT EDIT:** `Basic.lean`, `Main.lean`, `IntegralCurrents.lean`

---

### Track A5: Kähler Geometry (9 sorries)

**Files:**
- `Hodge/Kahler/Cone.lean` (5 sorries)
- `Hodge/Kahler/Microstructure.lean` (3 sorries)
- `Hodge/Kahler/TypeDecomposition.lean` (1 sorry)

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

**DO NOT EDIT:** `Basic.lean`, `Main.lean`, `Kahler/Main.lean`

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
