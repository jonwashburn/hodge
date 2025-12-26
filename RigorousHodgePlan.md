# Rigorous Formalization Plan: Hodge Conjecture (Sorry-Free, Three-Track)

**Goal:** Provide a machine-checked, machine-verified proof of the Hodge Conjecture using the "Calibration–Coercivity" framework, grounded in Mathlib primitives without `sorry`, `admit`, or `axiom` shortcuts.

**Philosophy:** Every mathematical fact—including "classical" theorems like Harvey-Lawson, GAGA, and Federer-Fleming—must be derived from type theory or have explicit, well-typed axiom declarations with documented assumptions.

---

## 🚦 Current Status Summary

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Analytic Foundations (Currents) | ⚠️ Partial (has `sorry`) |
| 2 | Kähler Linear Algebra (Cone Geometry) | ⚠️ Partial (has `sorry`) |
| 3 | Unconditional Reductions | ⚠️ Partial (has `sorry`) |
| 4 | Microstructure Construction | ⚠️ Partial (has `axiom`) |
| 5 | Global Gluing & Transport | ⚠️ Partial (has `sorry`) |
| 6 | Final Integration | ⚠️ Partial (has `sorry`) |

**Total `sorry` count:** ~25  
**Total `axiom` count:** 2 (Harvey-Lawson, L bundle placeholder)

---

## 🔀 Three Parallel Tracks

We organize the formalization into three concurrent tracks that can be developed simultaneously. Each track has clear interfaces and dependencies.

### Track A: Classical Axioms Foundation (`Hodge/Classical/`)
*Formalize the deep theorems from complex/algebraic geometry and GMT that are not in Mathlib.*

### Track B: Analytic/GMT Core (`Hodge/Analytic/`)
*Build the machinery for currents, mass norms, calibrations, and compactness theorems.*

### Track C: Algebraic/Kähler Core (`Hodge/Kahler/`)
*Kähler geometry, cone geometry, signed decomposition, and the main proof assembly.*

---

## 🏛️ Track A: Classical Axioms Foundation

**Directory:** `Hodge/Classical/`

These are the "deep" theorems that require substantial background. We formalize them with explicit axiom types, documenting all hypotheses, so they can later be proved or remain as trusted axioms with clear contracts.

### A.1 Harvey-Lawson Theorem (`Hodge/Classical/HarveyLawson.lean`)
**Status:** ❌ Currently an axiom in `Main.lean`

**Mathematical Statement:**  
A calibrated integral current on a Kähler manifold is integration along a positive sum of complex analytic subvarieties.

**Formalization Strategy:**
```lean
/-- The Harvey-Lawson structure theorem.
AXIOM TYPE: This is a deep result from [Harvey-Lawson, Acta Math 1982].
Dependencies: calibration theory, integral currents, analytic varieties. -/
structure HarveyLawsonData (X : Type*) [KahlerManifold X] where
  T : IntegralCurrent X
  ψ : CalibratingForm X
  h_calibrated : is_calibrated T ψ
  h_cycle : is_cycle T

/-- The Harvey-Lawson conclusion: existence of analytic representation. -/
def HarveyLawsonConclusion (data : HarveyLawsonData X) : Prop :=
  ∃ (V : Finset (AnalyticSubvariety X)) (mult : V → ℕ+),
    T = ∑ v in V, (mult v : ℤ) • integration_current v

/-- AXIOM: Harvey-Lawson theorem. -/
axiom harvey_lawson_theorem : ∀ (data : HarveyLawsonData X), HarveyLawsonConclusion data
```

**Sub-tasks:**
- [ ] A.1.1: Define `AnalyticSubvariety` rigorously
- [ ] A.1.2: Define `integration_current` (current of integration along a variety)
- [ ] A.1.3: Define `is_calibrated` predicate
- [ ] A.1.4: State the axiom with full type structure

---

### A.2 Serre's GAGA (`Hodge/Classical/GAGA.lean`)
**Status:** ❌ Currently has `sorry`

**Mathematical Statement:**  
Every complex analytic subvariety of a projective variety is algebraic.

**Formalization Strategy:**
```lean
/-- AXIOM TYPE: Serre's GAGA (Géométrie Algébrique et Géométrie Analytique).
Reference: [Serre, Ann. Inst. Fourier 1956]. -/
structure GAGAData (X : Type*) [ProjectiveVariety X] where
  V : Set X
  h_analytic : is_analytic_subvariety V

axiom serre_gaga : ∀ (data : GAGAData X), ∃ (W : AlgebraicSubvariety X), W.carrier = data.V
```

**Sub-tasks:**
- [ ] A.2.1: Define `ProjectiveVariety` (embedding into projective space)
- [ ] A.2.2: Define `is_analytic_subvariety` (local zero sets of holomorphic functions)
- [ ] A.2.3: Define `AlgebraicSubvariety` (zero sets of polynomials/global sections)
- [ ] A.2.4: State the axiom with coherent types

---

### A.3 Federer-Fleming Compactness (`Hodge/Classical/FedererFleming.lean`)
**Status:** ❌ Currently has `sorry`

**Mathematical Statement:**  
The space of integral currents with bounded mass and boundary mass is compact in the flat norm topology.

**Formalization Strategy:**
```lean
/-- AXIOM TYPE: Federer-Fleming Compactness Theorem.
Reference: [Federer-Fleming, Ann. Math 1960]. -/
structure FFCompactnessHypothesis (X : Type*) [RiemannianManifold X] (k : ℕ) where
  T : ℕ → IntegralCurrent k X
  M : ℝ
  h_mass_bound : ∀ n, mass (T n) + mass (boundary (T n)) ≤ M

axiom federer_fleming_compactness :
  ∀ (hyp : FFCompactnessHypothesis X k),
    ∃ (T_limit : IntegralCurrent k X) (φ : ℕ → ℕ),
      StrictMono φ ∧
      Filter.Tendsto (λ n => flat_norm (hyp.T (φ n) - T_limit)) Filter.atTop (nhds 0)
```

**Sub-tasks:**
- [ ] A.3.1: Define `flat_norm` rigorously using infimum
- [ ] A.3.2: Prove `flat_norm` is a norm (non-negativity, triangle inequality)
- [ ] A.3.3: Define `IntegralCurrent` as a structure with explicit multiplicity function
- [ ] A.3.4: State compactness axiom with full hypothesis structure

---

### A.4 Hard Lefschetz Theorem (`Hodge/Classical/Lefschetz.lean`)
**Status:** ❌ Not yet formalized

**Mathematical Statement:**  
For a Kähler manifold $(X, \omega)$ of dimension $n$, the map $L^{n-p} : H^p(X) \to H^{2n-p}(X)$ is an isomorphism for $p \leq n$.

**Formalization Strategy:**
```lean
/-- AXIOM TYPE: Hard Lefschetz Theorem.
Reference: [Griffiths-Harris, Principles of Algebraic Geometry]. -/
structure HardLefschetzData (X : Type*) [KahlerManifold X] where
  p : ℕ
  h_range : p ≤ dim X

axiom hard_lefschetz :
  ∀ (data : HardLefschetzData X),
    Function.Bijective (lefschetz_map (dim X - data.p) : H^data.p X → H^(2 * dim X - data.p) X)
```

**Sub-tasks:**
- [ ] A.4.1: Define cohomology groups `H^p X` (de Rham or singular)
- [ ] A.4.2: Define the Lefschetz operator `L : H^p → H^{p+2}`
- [ ] A.4.3: Define `lefschetz_map` as iteration of L
- [ ] A.4.4: State the axiom

---

### A.5 Bergman Kernel Asymptotics (`Hodge/Classical/Bergman.lean`)
**Status:** ❌ Currently has `axiom` and `sorry`

**Mathematical Statement:**  
Tian's theorem: The Bergman metric on $L^M$ converges to the Kähler metric in $C^2$ as $M \to \infty$.

**Sub-tasks:**
- [ ] A.5.1: Define line bundles and their tensor powers
- [ ] A.5.2: Define holomorphic sections (Bergman space)
- [ ] A.5.3: Define Bergman kernel and Bergman metric
- [ ] A.5.4: State Tian's convergence axiom
- [ ] A.5.5: Derive jet surjectivity as a consequence

---

### A.6 Serre Vanishing (`Hodge/Classical/SerreVanishing.lean`)
**Status:** ❌ Not yet formalized

**Mathematical Statement:**  
For an ample line bundle $L$ on a projective variety $X$, $H^q(X, L^M \otimes \mathcal{F}) = 0$ for $q > 0$ and $M \gg 0$.

**Sub-tasks:**
- [ ] A.6.1: Define coherent sheaves
- [ ] A.6.2: Define sheaf cohomology (or use Čech)
- [ ] A.6.3: Define ampleness
- [ ] A.6.4: State vanishing axiom

---

## 🔬 Track B: Analytic/GMT Core

**Directory:** `Hodge/Analytic/` (refactoring `Currents.lean` and `SYR.lean`)

### B.1 Differential Forms (`Hodge/Analytic/Forms.lean`)
**Status:** ⚠️ Uses Mathlib but needs cleanup

**Sub-tasks:**
- [ ] B.1.1: Import and alias `Mathlib.Geometry.Manifold.DifferentialForm`
- [ ] B.1.2: Define `Form k := DifferentialForm 𝓒(Complex, n) X k`
- [ ] B.1.3: Prove exterior derivative properties (`d ∘ d = 0`)
- [ ] B.1.4: Define Hodge star operator (depends on metric)

---

### B.2 Norms and Metrics (`Hodge/Analytic/Norms.lean`)
**Status:** ⚠️ Has `sorry` in `pointwise_comass` continuity

**Sub-tasks:**
- [ ] B.2.1: Define `kahler_metric` from `KahlerStructure.omega`
- [ ] B.2.2: Prove `kahler_metric` is an inner product (positive definite, symmetric)
- [ ] B.2.3: Define `pointwise_comass` using Mathlib's `sSup`
- [ ] B.2.4: **CRITICAL:** Prove continuity of `pointwise_comass`
- [ ] B.2.5: Define global `comass` as supremum
- [ ] B.2.6: Prove `comass_exists` (bounded on compact manifolds)

---

### B.3 Currents (`Hodge/Analytic/Currents.lean`)
**Status:** ⚠️ Core definitions exist but have `sorry`

**Sub-tasks:**
- [ ] B.3.1: Define `Current k` as continuous linear functional on `Form k`
- [ ] B.3.2: Define `mass` as dual norm to `comass`
- [ ] B.3.3: Prove `mass_neg : mass (-G) = mass G` ✓ (done)
- [ ] B.3.4: Prove `mass_add_le : mass (S + G) ≤ mass S + mass G` (has sorry)
- [ ] B.3.5: Define `boundary` operator via duality with `d`
- [ ] B.3.6: Prove `boundary ∘ boundary = 0`

---

### B.4 Integral Currents (`Hodge/Analytic/IntegralCurrents.lean`)
**Status:** ⚠️ Needs rigorous definition

**Sub-tasks:**
- [ ] B.4.1: Define `is_rectifiable_set` using Hausdorff measure
- [ ] B.4.2: Define `IntegralCurrent` as a structure with:
  - Rectifiable support
  - Integer multiplicity function
  - Finite mass
- [ ] B.4.3: Prove integral currents are closed under addition
- [ ] B.4.4: Prove boundary of integral current is integral

---

### B.5 Flat Norm and Compactness (`Hodge/Analytic/FlatNorm.lean`)
**Status:** ❌ Definition exists, properties missing

**Sub-tasks:**
- [ ] B.5.1: Prove `flat_norm` is non-negative
- [ ] B.5.2: Prove `flat_norm` satisfies triangle inequality
- [ ] B.5.3: Prove `flat_norm ≤ mass` for cycles
- [ ] B.5.4: Prove flat norm convergence implies weak-* convergence
- [ ] B.5.5: Interface with A.3 (Federer-Fleming) axiom

---

### B.6 Calibration Theory (`Hodge/Analytic/Calibration.lean`)
**Status:** ⚠️ Partially in `SYR.lean`

**Sub-tasks:**
- [ ] B.6.1: Define `is_calibrating_form ψ` (closed, comass ≤ 1)
- [ ] B.6.2: Define `is_calibrated T ψ` (mass T = T ψ)
- [ ] B.6.3: Prove `spine_theorem_bound` completely (has `sorry`)
- [ ] B.6.4: Prove `limit_is_calibrated` completely (has `sorry`)

---

## ⚡ Track C: Algebraic/Kähler Core

**Directory:** `Hodge/Kahler/` (refactoring `Basic.lean`, `ConeGeometry.lean`, `Reductions.lean`)

### C.1 Manifold Foundations (`Hodge/Kahler/Manifolds.lean`)
**Status:** ⚠️ Definitions exist with placeholders

**Sub-tasks:**
- [ ] C.1.1: Define `ProjectiveComplexManifold` with explicit embedding
- [ ] C.1.2: Prove projective implies compact (use Mathlib's `CompactSpace`)
- [ ] C.1.3: Define `KahlerStructure` with:
  - Symplectic form `ω`
  - Proof that `dω = 0`
  - Proof that `ω(v, Jv) > 0`
- [ ] C.1.4: Define `is_rational` for cohomology classes

---

### C.2 Type Decomposition (`Hodge/Kahler/TypeDecomposition.lean`)
**Status:** ⚠️ Basic definition exists

**Sub-tasks:**
- [ ] C.2.1: Define `(p,q)`-forms via $J$-eigenspaces
- [ ] C.2.2: Prove `Ω^k = ⊕_{p+q=k} Ω^{p,q}` (Hodge decomposition)
- [ ] C.2.3: Define `is_p_p_form` via $J$-invariance
- [ ] C.2.4: Prove `ω^p` is a `(p,p)`-form

---

### C.3 Strongly Positive Cone (`Hodge/Kahler/Cone.lean`)
**Status:** ⚠️ Definition exists, key lemmas have `sorry`

**Sub-tasks:**
- [ ] C.3.1: Define `simple_calibrated_forms p x` (unit volume forms of $p$-planes)
- [ ] C.3.2: Define `strongly_positive_cone p x` as `convexHull`
- [ ] C.3.3: Prove `strongly_positive_cone` is a proper convex cone
- [ ] C.3.4: **CRITICAL:** Prove `omega_pow_in_interior`
- [ ] C.3.5: Prove uniform interior radius exists (for compact $X$)
- [ ] C.3.6: Prove Carathéodory decomposition (from Mathlib)

---

### C.4 Signed Decomposition (`Hodge/Kahler/SignedDecomp.lean`)
**Status:** ⚠️ Statement exists, proof has `sorry`

**Sub-tasks:**
- [ ] C.4.1: Prove `form_is_bounded` using Extreme Value Theorem
- [ ] C.4.2: Prove `exists_uniform_interior_radius`
- [ ] C.4.3: **CRITICAL:** Complete `signed_decomposition` proof
- [ ] C.4.4: Prove `omega_pow_is_algebraic` (complete intersections)

---

### C.5 Microstructure (`Hodge/Kahler/Microstructure.lean`)
**Status:** ⚠️ Has `axiom` for line bundle

**Sub-tasks:**
- [ ] C.5.1: Define `AmpleLineBundle` structure
- [ ] C.5.2: Use A.5 (Bergman) and A.6 (Serre Vanishing) for jet surjectivity
- [ ] C.5.3: Prove `local_sheet_realization`
- [ ] C.5.4: Define `Cubulation` properly
- [ ] C.5.5: Prove `integer_transport_flow` (total unimodularity)

---

### C.6 Main Theorem (`Hodge/Kahler/Main.lean`)
**Status:** ⚠️ Logical structure exists, needs completion

**Sub-tasks:**
- [ ] C.6.1: Wire together Track A axioms
- [ ] C.6.2: Wire together Track B analytic machinery
- [ ] C.6.3: Assemble the SYR chain:
  - Signed decomposition → cone-positive + algebraic
  - Microstructure → integral cycles with vanishing defect
  - Federer-Fleming → integral limit
  - Limit calibration → calibrated limit
  - Harvey-Lawson → analytic variety
  - GAGA → algebraic cycle
- [ ] C.6.4: Close the $p > n/2$ case via Hard Lefschetz

---

## 📊 Dependency Graph

```
                    ┌──────────────────────────────────────────┐
                    │            TRACK A: AXIOMS               │
                    │  Harvey-Lawson │ GAGA │ FF │ Lefschetz   │
                    │       Bergman  │ Serre Vanishing         │
                    └───────────┬────────────────┬─────────────┘
                                │                │
        ┌───────────────────────┴────┐     ┌─────┴─────────────────────┐
        │     TRACK B: ANALYTIC      │     │   TRACK C: KAHLER         │
        │  Forms → Norms → Currents  │     │  Manifolds → Type Decomp  │
        │  IntegralCurrents → Flat   │     │  Cone → SignedDecomp      │
        │  Calibration               │     │  Microstructure           │
        └───────────────┬────────────┘     └─────────────┬─────────────┘
                        │                                │
                        └────────────────┬───────────────┘
                                         │
                            ┌────────────▼────────────┐
                            │   MAIN THEOREM          │
                            │   (hodge_conjecture)    │
                            └─────────────────────────┘
```

---

## 📝 Rules for the Assistant

1. **No Shortcuts**: Do not use `sorry`, `admit` except as explicit `-- TODO` markers during development.
2. **Axiom Discipline**: Every `axiom` must:
   - Have a docstring citing the original reference
   - Use a structured hypothesis type (not raw props)
   - Be placed in `Hodge/Classical/`
3. **Library First**: Check for existing Mathlib definitions before creating new ones.
4. **Small Batches**: Implement 1-2 lemmas/definitions per turn and verify they compile.
5. **Trace Dependencies**: Every definition in `Main.lean` must trace back to `Basic.lean` and Mathlib.
6. **Interface Discipline**: Each track should export clean interfaces that other tracks can import.

---

## 🔄 Parallel Development Protocol

1. **Track A** can proceed independently—defining axiom structures and types.
2. **Track B** can proceed independently—building analytic machinery.
3. **Track C** depends on interfaces from A and B but can develop internal structure.
4. **Integration** happens in `Main.lean` once all tracks are complete.

### Recommended Starting Points (Parallel)

| Track | First Task | File |
|-------|------------|------|
| A | Define `AnalyticSubvariety` and `integration_current` | `Hodge/Classical/HarveyLawson.lean` |
| B | Complete `mass_add_le` proof | `Hodge/Analytic/Currents.lean` |
| C | Complete `omega_pow_in_interior` proof | `Hodge/Kahler/Cone.lean` |

---

## 📈 Progress Tracking

### Track A Progress
- [ ] A.1: Harvey-Lawson (0/4 subtasks)
- [ ] A.2: GAGA (0/4 subtasks)
- [ ] A.3: Federer-Fleming (0/4 subtasks)
- [ ] A.4: Hard Lefschetz (0/4 subtasks)
- [ ] A.5: Bergman (0/5 subtasks)
- [ ] A.6: Serre Vanishing (0/4 subtasks)

### Track B Progress
- [ ] B.1: Forms (0/4 subtasks)
- [ ] B.2: Norms (0/6 subtasks)
- [ ] B.3: Currents (0/6 subtasks)
- [ ] B.4: Integral Currents (0/4 subtasks)
- [ ] B.5: Flat Norm (0/5 subtasks)
- [ ] B.6: Calibration (0/4 subtasks)

### Track C Progress
- [ ] C.1: Manifolds (0/4 subtasks)
- [ ] C.2: Type Decomposition (0/4 subtasks)
- [ ] C.3: Cone (0/6 subtasks)
- [ ] C.4: Signed Decomposition (0/4 subtasks)
- [ ] C.5: Microstructure (0/5 subtasks)
- [ ] C.6: Main Theorem (0/4 subtasks)

---

## 🎯 Milestone Targets

1. **M1: Axiom Foundation Complete** — All Track A axioms stated with proper types
2. **M2: Analytic Core Complete** — All Track B proofs done (no `sorry`)
3. **M3: Kähler Core Complete** — All Track C proofs done (no `sorry`)
4. **M4: Integration Complete** — `hodge_conjecture` compiles with only Track A axioms
5. **M5: Sorry-Free** — No `sorry` anywhere; only documented `axiom` declarations

---

*Last updated: 2024-12-26*
