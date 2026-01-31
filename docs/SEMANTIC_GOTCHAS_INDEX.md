# Semantic Gotchas Index (Proof-Track Blockers)

This file is a **living index** of remaining “no gotchas” blockers: definitions and instances that still trivialize the intended mathematics even though the repo currently compiles and the audits are green.

The intent is to make it easy for the integrator (and bounded agents) to find and eliminate semantic cheats without “passing the audit by changing the audit”.

---

## A. Cycle class / fundamental class

- **`SignedAlgebraicCycle.cycleClass_geom` is still an alias of `cycleClass`**
  - File: `Hodge/Classical/GAGA.lean`
  - Symptom: `cycleClass_geom` is currently defined as `Z.cycleClass` (representing form), so `hodge_conjecture'` ends with `rfl`.
  - Required fix: `cycleClass_geom` must be computed from the **support** via fundamental class / integration current, not from the carried form.

- **`FundamentalClassSet` is still a placeholder (PD form machinery is stubby)**
  - File: `Hodge/Classical/GAGA.lean` (`FundamentalClassSet_impl`, `FundamentalClassSet`)
  - File: `Hodge/Classical/CycleClass.lean` (`PoincareDualFormExists.universal`, `omegaPower`, `fundamentalClassImpl`)
  - Symptom: PD forms are currently “constructed” by a heuristic like `ω^p` (or other non-geometric selection), not by integration current / PD.

---

## A0. Foundational modeling gap: “forms live in the wrong fiber”

Even before integration/GAGA/HL, the current proof track’s differential-form model is not the real one:

- In `Hodge/Basic.lean`, `FiberAlt n k` is defined as a space of **ℂ-linear** alternating maps on `ℂⁿ`.
  This forces `FiberAlt n k` (hence `SmoothForm n X k`) to be **trivial for k > n** (complex dimension),
  whereas the real de Rham theory on a complex n-fold needs nontrivial degrees up to **2n**.

This is why the repo can “talk about 2n-forms” while many constructions collapse.

**No-gotchas requirement**: the proof track must ultimately use a real de Rham model:
- forms are alternating **ℝ-multilinear** maps on the underlying real tangent (real dimension 2n),
  with coefficients in ℂ (or ℝ).

This change is deep and will require a staged migration (new `FiberAltR` / `SmoothFormR` layer + rewriting
`smoothExtDeriv`, wedge, norms, and all cohomology definitions).

---

## B. Submanifold integration / Stokes (deep GMT layer)

- **`SubmanifoldIntegration.universal` is the zero-measure/zero-integral model**
  - File: `Hodge/Analytic/Integration/HausdorffMeasure.lean`
  - Symptom: `measure2p := 0`, `integral := 0`, Stokes holds by simp.
  - Required fix: replace with genuine integration theory.

- **`SubmanifoldIntegration.real` still has `integral := 0`**
  - File: `Hodge/Deep/Pillars/Stokes.lean`
  - Symptom: even though `measure2p := μH (2*p)` is real Hausdorff measure, the integral is still identically zero.

---

## C. SYR microstructure (deep construction)

- **Microstructure sequence is still constant zero**
  - File: `Hodge/Kahler/Microstructure/RealSpine.lean`
    - `microstructureSequence_real := fun _k => zero_int ...`
    - `microstructureSequence_real_defect_vanishes` proves defect→0 only because the sequence is constant 0.
  - File: `Hodge/Kahler/Main.lean`
    - `AutomaticSYRData.universal` builds the zero current sequence.
  - Required fix: implement actual sheets + gluing + defect bound.

- **Sheet construction is still empty / support is still `Set.univ` in the proof-track builder**
  - File: `Hodge/Kahler/Microstructure.lean`
    - `buildSheetsFromConePositive`: `sheets := ∅`, `support := Set.univ`
  - Required fix: nontrivial holomorphic sheet construction and a true support set.

---

## D. Harvey–Lawson / King

- **Analytic variety output is not yet real analytic geometry**
  - File: `Hodge/Classical/HarveyLawson.lean`
  - Symptom: “analytic set” infrastructure is still not tied to local holomorphic zero loci.

---

## E. Chow / GAGA

- **Algebraic sets are currently approximated by closed sets**
  - File: `Hodge/Classical/GAGA.lean`
  - Symptom: `IsAlgebraicSet` is defined as topological closedness (explicitly documented in-file).
  - This is explicitly forbidden by the “no gotchas” spec; must be replaced by real algebraic definitions.

---

## F. Proof-track gotcha: local injection of universal instances

Even if binder scans are clean, the proof can still be “powered” by internal `letI := ...universal` injections.

- File: `Hodge/Kahler/Main.lean`
  - `hodge_conjecture'` currently sets local instances:
    - `SubmanifoldIntegration.universal`
    - `AutomaticSYRData.universal`
    - `FlatLimitCycleData.universal`
    - `HarveyLawsonKingData.universal`
    - `ChowGAGAData.universal`
  - and concludes with `rfl` because `cycleClass_geom` is aliased.

Required fix:
- remove these universal injections by replacing them with **proved** instances / direct theorems, and eliminate the `rfl` endpoint by making `cycleClass_geom` geometric.

---

## G. Recent real progress (not gotchas)

These are **real lemmas** that directly support the TeX spine around your current TeX location:

- `Hodge/GMT/TemplateExtension.lean`
  - `Hodge.TexSpine.Template.prefix_mismatch_decompose`
  - `Hodge.TexSpine.TemplateFlat.flatNorm_prefix_mismatch_le_unmatched`
- `Hodge/GMT/TransportFlat.lean`
  - `Hodge.TexSpine.TransportFlat.flatNorm_finSum_le_of_piecewise_decomp`
  - `Hodge.TexSpine.TransportFlat.flatNorm_mismatch_le_of_perm`

These are purely formal (no geometry cheated) and will be used when replacing the `zero_int` microstructure stub with real gluing.

