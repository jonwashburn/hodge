# Agent Assignments: 35 Axioms to Prove

**Mission:** Prove all 35 axioms in `hodge_conjecture'` proof chain.

**Success:** `#print axioms hodge_conjecture'` shows only `propext`, `Classical.choice`, `Quot.sound` (+ optionally `serre_gaga`).

---

## 🚫 RULES

1. **NO `sorry`, `admit`, `trivial`, `native_decide`**
2. **NO stub definitions** (`def mass := 0` is NOT a proof)
3. **Build passes before claiming done:** `lake build Hodge`
4. **Verify axiom removed:** `lake env lean DependencyCheck.lean`

---

## Current Status

| Metric | Value |
|--------|-------|
| Build | ✅ Passes |
| Axioms in proof chain | **35** |
| Target | **0** (or 1 with `serre_gaga`) |

---

# 🔷 AGENT 1: Form Structure + Quotient (12 axioms)

## Files: `Hodge/Basic.lean`

## Your Axioms

| # | Axiom | Priority | Strategy |
|---|-------|----------|----------|
| 24 | `SmoothForm.zero` | P5 | Interface for opaque type |
| 25 | `SmoothForm.instAddCommGroup` | P5 | Interface for opaque type |
| 26 | `SmoothForm.instModuleComplex` | P5 | Interface for opaque type |
| 27 | `SmoothForm.instTopologicalSpace` | P5 | Interface for opaque type |
| 28 | `smoothExtDeriv_add` | P5 | d is linear |
| 29 | `smoothExtDeriv_smul` | P5 | d is linear |
| 30 | `smoothExtDeriv_smul_real` | P5 | d is linear |
| 31 | `instAddCommGroupDeRhamCohomologyClass` | P5 | Quotient.lift₂ |
| 32 | `instModuleDeRhamCohomologyClass` | P5 | Quotient.lift |
| 33 | `ofForm_add` | P6 | **START HERE** |
| 34 | `ofForm_sub` | P6 | Quotient.sound |
| 35 | `ofForm_smul_real` | P6 | Quotient.sound |

## Priority Order

1. **#33-35 (ofForm operations)** — Most likely to succeed
2. **#31-32 (cohomology instances)** — Use Quotient.lift₂
3. **#28-30 (smoothExtDeriv linearity)** — Requires d to be defined
4. **#24-27 (SmoothForm instances)** — Interface axioms, hardest

## Proof Pattern for ofForm

```lean
theorem ofForm_add {k : ℕ} (ω η : SmoothForm n X k) 
    (hω : IsFormClosed ω) (hη : IsFormClosed η) :
    DeRhamCohomologyClass.ofForm (ω + η) (isFormClosed_add hω hη) =
    DeRhamCohomologyClass.ofForm ω hω + DeRhamCohomologyClass.ofForm η hη := by
  -- The addition on DeRhamCohomologyClass is defined via the quotient
  -- ofForm ω hω = ⟦⟨ω, hω⟩⟧
  -- Need to show: ⟦⟨ω + η, _⟩⟧ = ⟦⟨ω, hω⟩⟧ + ⟦⟨η, hη⟩⟧
  -- This should follow from how + is defined on the quotient
  rfl  -- or use Quotient.sound if needed
```

---

# 🔷 AGENT 2: Flat Norm / Mass (7 axioms)

## Files: `Hodge/Analytic/FlatNorm.lean`, `Hodge/Analytic/Currents.lean`, `Hodge/Analytic/Calibration.lean`

## Your Axioms

| # | Axiom | File | Strategy |
|---|-------|------|----------|
| 7 | `eval_le_flatNorm` | FlatNorm.lean | Duality estimate |
| 8 | `flatNorm_boundary_le` | FlatNorm.lean | ‖∂T‖_F ≤ ‖T‖_F |
| 9 | `flatNorm_eq_zero_iff` | FlatNorm.lean | Characterization |
| 10 | `flatNorm_neg` | FlatNorm.lean | **START HERE** |
| 11 | `mass_lsc` | Calibration.lean | Classical (LSC) |
| 12 | `Current.mass_nonneg` | Currents.lean | **START HERE** |
| 13 | `Current.mass_zero` | Currents.lean | **START HERE** |

## Priority Order

1. **#12-13 (mass properties)** — Basic norm properties
2. **#10 (flatNorm_neg)** — Symmetry
3. **#9 (flatNorm_eq_zero_iff)** — Characterization
4. **#7-8, #11** — May need more infrastructure

## Proof Patterns

```lean
theorem Current.mass_nonneg (T : Current n X k) : mass T ≥ 0 := by
  -- mass is opaque, but defined as supremum of evaluations
  -- All evaluations bounded by comass, all nonneg
  sorry -- Check if there's a defining property we can use

theorem flatNorm_neg (T : Current n X k) : flatNorm (-T) = flatNorm T := by
  -- flatNorm T = inf { mass S + mass R | T = S + ∂R }
  -- For -T: -T = -S + ∂(-R), same infimum by symmetry
  sorry -- Use symmetry of the decomposition
```

---

# 🔷 AGENT 3: Kähler / Calibration (10 axioms)

## Files: `Hodge/Analytic/Calibration.lean`, `Hodge/Analytic/Grassmannian.lean`, `Hodge/Kahler/Cone.lean`, `Hodge/Kahler/TypeDecomposition.lean`, `Hodge/Analytic/Norms.lean`

## Your Axioms

| # | Axiom | File | Strategy |
|---|-------|------|----------|
| 14 | `wirtinger_comass_bound` | Calibration.lean | Wirtinger inequality |
| 15 | `calibration_inequality` | Calibration.lean | T(ψ) ≤ mass(T) |
| 16 | `simpleCalibratedForm` | Grassmannian.lean | Volume form exists |
| 17 | `omegaPow_in_interior` | Cone.lean | ω^p in interior |
| 18 | `omega_pow_IsFormClosed` | TypeDecomp.lean | **START HERE** |
| 19 | `omega_pow_is_rational` | TypeDecomp.lean | [ω^p] ∈ H(X,ℚ) |
| 20 | `omega_pow_represents_multiple` | Main.lean | Hyperplane section |
| 21 | `shift_makes_conePositive_rat` | Cone.lean | γ + c·ω^p positive |
| 22 | `conePositive_comass_bound` | Cone.lean | Comass bound |
| 23 | `pointwiseComass_nonneg` | Norms.lean | **START HERE** |

## Priority Order

1. **#18 (omega_pow_IsFormClosed)** — d(ω^p) = 0 by induction
2. **#23 (pointwiseComass_nonneg)** — Supremum of abs values ≥ 0
3. **#15 (calibration_inequality)** — Definition of calibration
4. Others — Need more infrastructure

## Proof Patterns

```lean
theorem omega_pow_IsFormClosed (p : ℕ) : 
    IsFormClosed (kahlerPow (n := n) (X := X) p) := by
  induction p with
  | zero => 
    -- ω^0 = 1 (unit form), d(1) = 0
    exact isFormClosed_one  -- or however unit is defined
  | succ p ih =>
    -- ω^{p+1} = ω ∧ ω^p
    -- d(ω ∧ ω^p) = dω ∧ ω^p ± ω ∧ d(ω^p) = 0 ∧ ω^p ± ω ∧ 0 = 0
    apply isFormClosed_wedge
    · exact KahlerManifold.omega_closed  -- dω = 0
    · exact ih

theorem pointwiseComass_nonneg {ω : SmoothForm n X k} {x : X} : 
    pointwiseComass ω x ≥ 0 := by
  -- pointwiseComass = sup { |ω(v₁,...,vₖ)| / |v₁ ∧ ... ∧ vₖ| }
  -- Supremum of nonnegative quantities is nonnegative
  apply Real.sSup_nonneg
  intro y hy
  exact abs_nonneg _
```

---

# 🔷 AGENT 4: Strategy-Critical (2 axioms)

## Files: `Hodge/Kahler/Main.lean`

## Your Axioms

| # | Axiom | Line | Strategy |
|---|-------|------|----------|
| 1 | `harvey_lawson_fundamental_class` | Main.lean:112 | **HARDEST** |
| 2 | `lefschetz_lift_signed_cycle` | Main.lean:195 | **HARDEST** |

## These Are the Key Blockers

### Investigation Tasks

1. **Read Main.lean:100-220** carefully
2. **Check what `harvey_lawson_theorem` provides** — currently returns empty varieties
3. **Check what `hard_lefschetz_inverse_form` provides**
4. **Determine if these can be derived from existing structure**

### Options

**Option A: Build Real Infrastructure**
- Fix `harvey_lawson_theorem` to return actual varieties
- This requires GMT regularity theory

**Option B: Derive from Existing Axioms**
- Check if the types align such that we can compose existing axioms
- May need additional lemmas

**Option C: Document as Classical Pillars**
- These are deep theorems (Harvey-Lawson 1982, Voisin 2002)
- If truly infeasible, document and accept as classical pillars

### What These Axioms Say

```lean
-- #1: If T_limit represents the Harvey-Lawson conclusion, 
-- then the fundamental class of the union equals the cohomology class
axiom harvey_lawson_fundamental_class {p : ℕ}
    (γ : SmoothForm n X (2 * p)) (hγ : IsFormClosed γ)
    (hcone : isConePositive γ)
    (hl_concl : HarveyLawsonConclusion n X (2 * (n - p)))
    (T_limit : Current n X (2 * (n - p)))
    (h_rep : hl_concl.represents T_limit) :
    ⟦FundamentalClassSet ..., _⟧ = ⟦γ, hγ⟧

-- #2: If η is represented by a signed algebraic cycle,
-- then the Lefschetz preimage γ is also representable
axiom lefschetz_lift_signed_cycle {p p' : ℕ}
    (γ η : SmoothForm ...) (Z_η : SignedAlgebraicCycle n X)
    (hp : p > n / 2)
    (h_rep : Z_η.RepresentsClass (ofForm η hη)) :
    ∃ Z, Z.RepresentsClass (ofForm γ hγ)
```

---

# 🔷 AGENT 5: Microstructure + GAGA (5 axioms)

## Files: `Hodge/Kahler/Microstructure.lean`, `Hodge/Classical/GAGA.lean`

## Your Axioms

| # | Axiom | File | Strategy |
|---|-------|------|----------|
| 3 | `calibration_defect_from_gluing` | Microstructure.lean | Paper Section 11 |
| 4 | `gluing_mass_bound` | Microstructure.lean | Paper Section 11 |
| 5 | `RawSheetSum.toIntegralCurrent_isCycle` | Microstructure.lean | **START HERE** |
| 6 | `flat_limit_existence` | Microstructure.lean | FF compactness |
| 36 | `serre_gaga` | GAGA.lean | **CLASSICAL PILLAR** |

## Priority Order

1. **#5 (RawSheetSum.toIntegralCurrent_isCycle)** — Prove ∂ = 0
2. **#3-4 (gluing bounds)** — From paper construction
3. **#6 (flat_limit_existence)** — May need to stay axiom
4. **#36 (serre_gaga)** — KEEP as classical pillar

## Proof Pattern for #5

```lean
theorem RawSheetSum.toIntegralCurrent_isCycle {p : ℕ} {hscale : ℝ}
    (rss : RawSheetSum n X p hscale) :
    boundary (RawSheetSum.toIntegralCurrent rss) = 0 := by
  -- The sheet sum is a linear combination of integration currents
  -- Each sheet is a closed oriented submanifold (or has boundary that cancels)
  -- When we sum with integer coefficients, boundaries cancel
  unfold RawSheetSum.toIntegralCurrent
  -- Expand and show boundary of sum = sum of boundaries = 0
  simp only [boundary_sum, boundary_smul]
  -- Each sheet boundary cancels...
  sorry
```

---

# Summary

| Agent | Axioms | Priority | Start With |
|-------|--------|----------|------------|
| **1** | 12 | P5, P6 | `ofForm_add`, `ofForm_sub` |
| **2** | 7 | P3 | `mass_nonneg`, `mass_zero`, `flatNorm_neg` |
| **3** | 10 | P4 | `omega_pow_IsFormClosed`, `pointwiseComass_nonneg` |
| **4** | 2 | P1 | Investigate `harvey_lawson_theorem` |
| **5** | 5 | P2, P7 | `RawSheetSum.toIntegralCurrent_isCycle` |

**Total:** 35 axioms → 0 target (or 1 with `serre_gaga`)

---

# Verification

After each session:
```bash
lake env lean DependencyCheck.lean 2>&1 | grep -E "^ " | grep -v "propext\|Classical.choice\|Quot.sound" | wc -l
```

**Current:** 35  
**Target:** 0 (or 1)
