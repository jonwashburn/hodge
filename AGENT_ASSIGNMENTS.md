# Agent Assignments: Phase 5 — Axiom Reduction Sprint

## 📊 CURRENT STATUS (Jan 3, 2026)

| Metric | Count |
|--------|-------|
| **Total Axioms** | 95 |
| **Sorries** | 3 |
| **Build Errors** | 2 files failing |

### Build Status
- ❌ `Hodge/Analytic/Norms.lean` — Type mismatches, unknown constants
- ❌ `Hodge/Classical/Lefschetz.lean` — Unknown identifiers, type mismatches

---

## 🚫 ABSOLUTE RULES
1. **NO `sorry`** — If you can't prove it, document the blocker.
2. **NO new `axiom`** — Convert existing axioms to theorems using Mathlib.
3. **Mathlib First** — Always check Mathlib for existing lemmas.

---

# 📋 AXIOM INVENTORY BY FILE

| File | Axioms | Priority |
|------|--------|----------|
| `Cohomology/Basic.lean` | 15 | HIGH |
| `Analytic/Forms.lean` | 11 | HIGH |
| `Kahler/Manifolds.lean` | 6 | MEDIUM |
| `Kahler/Microstructure.lean` | 6 | LOW (Deep) |
| `Analytic/Norms.lean` | 6 | HIGH (Broken) |
| `Analytic/Grassmannian.lean` | 6 | MEDIUM |
| `Basic.lean` | 4 | HIGH |
| `Analytic/SheafTheory.lean` | 4 | LOW |
| `Kahler/TypeDecomposition.lean` | 3 | MEDIUM |
| `Kahler/Main.lean` | 3 | MEDIUM |
| `Kahler/Cone.lean` | 3 | MEDIUM |
| `Classical/Bergman.lean` | 3 | LOW |
| Other files | 10 | LOW |

---

# 🔴 AGENT 1: Build Fixer (CRITICAL)

## Files Owned
- `Hodge/Analytic/Norms.lean`

## Mission
Fix the build errors in Norms.lean.

## Current Errors
```
error: Norms.lean:120:28: Type mismatch
error: Norms.lean:146:29: Unknown constant `BddAbove.of_sSup_eq`
error: Norms.lean:154:44: Type mismatch  
error: Norms.lean:226:2: Function expected at
error: Norms.lean:236:47: Fields missing: `smul_zero`, `smul_add`, `add_smul`, `zero_smul`
error: Norms.lean:238:4: 'show' tactic failed
```

## HOW TO FIX

### Line 120: `hf.norm` fails
**Problem:** `α.is_smooth` returns `True` (not a continuity proof).
**Fix:** Replace with an axiom or use:
```lean
axiom smoothForm_continuous {k : ℕ} (α : SmoothForm n X k) : 
    Continuous (fun x => α.as_alternating x)
```

### Line 146: `BddAbove.of_sSup_eq` unknown
**Problem:** This lemma doesn't exist in Mathlib.
**Fix:** Use instead:
```lean
have h_bdd : BddAbove (range (pointwiseComass α)) := by
  use comass α
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  exact le_csSup_of_le ⟨comass α, ...⟩ (mem_range_self x) (le_refl _)
```
Or convert to an axiom temporarily.

### Lines 236-238: Module instance fields missing
**Problem:** Constructing `Module ℂ (SmoothForm n X k)` needs all fields.
**Fix:** Use `inferInstance` if `SmoothForm` already has `Module` via its `AddCommGroup` + `SMul` structure, or define all required fields.

---

# 🔴 AGENT 2: Lefschetz Fixer (CRITICAL)

## Files Owned
- `Hodge/Classical/Lefschetz.lean`

## Mission
Fix the build errors in Lefschetz.lean.

## Current Errors
```
error: Lefschetz.lean:60:13: Type mismatch
error: Lefschetz.lean:64:10: Unknown identifier `cup_mul_add`
error: Lefschetz.lean:72:10: Unknown identifier `cup_mul_smul`
error: Lefschetz.lean:84:6: Application type mismatch
error: Lefschetz.lean:196:10: Function expected at
error: Lefschetz.lean:213:10: Function expected at
```

## HOW TO FIX

### Lines 64, 72: Unknown `cup_mul_add`, `cup_mul_smul`
**Problem:** These were renamed in `Cohomology/Basic.lean` to `mul_add` and `mul_smul`.
**Fix:** Replace:
```lean
-- Before
exact cup_mul_add ⟦K.omega_form, K.omega_closed⟧ η₁ η₂
-- After
exact mul_add ⟦K.omega_form, K.omega_closed⟧ η₁ η₂
```

### Line 60: Type mismatch
**Problem:** Degree arithmetic (`p + 2` vs `2 + p`).
**Fix:** Check if `HMul` expects `DeRhamCohomologyClass n X 2 * DeRhamCohomologyClass n X p → DeRhamCohomologyClass n X (2 + p)`.
Use `Nat.add_comm` to cast:
```lean
toFun c := (Nat.add_comm 2 p) ▸ (⟦K.omega_form, K.omega_closed⟧ * c)
```

---

# 🟡 AGENT 3: Cohomology Algebraist

## Files Owned
- `Hodge/Cohomology/Basic.lean`

## Mission
Prove the 15 axioms about cohomology class operations.

## Axiom List (15 total)
1. `cohomologous_symm` — Symmetry of cohomologous relation
2. `cohomologous_trans` — Transitivity of cohomologous relation
3. `instAddDeRhamCohomologyClass` — Add instance
4. `instNegDeRhamCohomologyClass` — Neg instance
5. `instSubDeRhamCohomologyClass` — Sub instance
6. `instAddCommGroupDeRhamCohomologyClass` — AddCommGroup instance
7. `instSMulComplexDeRhamCohomologyClass` — SMul ℂ instance
8. `instModuleComplexDeRhamCohomologyClass` — Module ℂ instance
9. `instSMulRationalDeRhamCohomologyClass` — SMul ℚ instance
10. `instHMulDeRhamCohomologyClass` — Cup product instance
11. `isRationalClass_sub` — Subtraction preserves rationality
12. `isRationalClass_mul` — Product preserves rationality
13. `mul_add`, `add_mul`, `mul_smul`, `smul_mul`, `zero_mul`, `mul_zero` — Ring properties
14. `ofForm_add`, `ofForm_smul`, `ofForm_smul_real`, `ofForm_sub`, `ofForm_wedge` — Quotient descent
15. `lefschetzL_add`, `lefschetzL_smul` — Lefschetz operator linearity

## HOW TO PROVE

### Cohomologous Symmetry/Transitivity
```lean
theorem cohomologous_symm {ω η : ClosedForm n X k} : 
    Cohomologous ω η → Cohomologous η ω := by
  intro ⟨θ, hθ⟩
  use -θ
  simp [smoothExtDeriv_neg, hθ]
```

### Quotient Instances
Use `Quotient.liftOn₂` for binary operations:
```lean
instance : Add (DeRhamCohomologyClass n X k) where
  add := Quotient.lift₂ 
    (fun ω η => ⟦ω.val + η.val, isFormClosed_add ω.property η.property⟧)
    (fun _ _ _ _ h1 h2 => Quotient.sound (cohomologous_add h1 h2))
```

---

# 🟡 AGENT 4: Forms Expert

## Files Owned
- `Hodge/Analytic/Forms.lean`

## Mission
Prove the 11 axioms about smooth forms.

## Axiom List (11 total)
1. `SmoothForm.instTopologicalSpace` — Topology on forms
2. `extDerivLinearMap` — d is a linear map
3. `isFormClosed_wedge` — Closed ⋏ Closed = Closed
4. `smoothExtDeriv_extDeriv` — d² = 0
5. `smoothExtDeriv_wedge` — Leibniz rule: d(α ⋏ β) = dα ⋏ β + (-1)^k α ⋏ dβ
6. `smoothWedge_add_left/right` — Wedge distributes over addition
7. `smoothWedge_smul_left/right` — Wedge is bilinear
8. `smoothWedge_zero_left/right` — 0 ⋏ η = 0

## HOW TO PROVE

### Wedge Linearity
These should follow from `AlternatingMap` properties:
```lean
theorem smoothWedge_add_left (ω₁ ω₂ : SmoothForm n X k) (η : SmoothForm n X l) :
    (ω₁ + ω₂) ⋏ η = (ω₁ ⋏ η) + (ω₂ ⋏ η) := by
  ext x
  simp only [SmoothForm.add_apply, smoothWedge_apply]
  -- AlternatingMap addition is pointwise
  sorry
```

### d² = 0
Use Mathlib's `d_d` or prove from the Cartan magic formula.

---

# 🟡 AGENT 5: Basic Infrastructure

## Files Owned
- `Hodge/Basic.lean`

## Mission
Prove the 4 axioms about TangentSpace norms.

## Axiom List (4 total)
1. `exists_not_isClosed_set` — Every space has a non-closed set
2. `instNormTangentSpace` — Norm on TangentSpace
3. `instNormedAddCommGroupTangentSpace` — NormedAddCommGroup structure
4. `instNormedSpaceTangentSpace` — NormedSpace structure

## HOW TO PROVE

### TangentSpace Norm Instances
These should follow from the fact that TangentSpace ≃ EuclideanSpace ℂ (Fin n):
```lean
noncomputable instance instNormTangentSpace (x : X) : Norm (TangentSpace (𝓒_complex n) x) :=
  inferInstanceAs (Norm (EuclideanSpace ℂ (Fin n)))
```

---

# 🟡 AGENT 6: Kähler Geometry

## Files Owned
- `Hodge/Kahler/Manifolds.lean`

## Mission
Prove the 6 Kähler form axioms.

## Axiom List (6 total)
1. `kahlerMetric_symm` — g(u,v) = g(v,u)
2. `lefschetzLambdaLinearMap` — Λ is linear
3. `lefschetz_commutator` — [L, Λ] = (n-k) on k-forms
4. `hodgeStar_*` — Hodge star operator properties
5. `adjointDeriv_*` — δ operator properties
6. `laplacian_*` — Δ operator properties

## HOW TO PROVE

### Hodge Star Properties
These are standard results from Hodge theory:
```lean
theorem hodgeStar_add (α β : SmoothForm n X k) : ⋆(α + β) = ⋆α + ⋆β := by
  ext x
  simp [hodgeStar_apply]
  -- Linear map property
  exact (hodgeStarOp x).map_add (α.as_alternating x) (β.as_alternating x)
```

---

# 🟢 AGENT 7: Grassmannian Geometry

## Files Owned
- `Hodge/Analytic/Grassmannian.lean`

## Mission
Prove the 6 Grassmannian axioms.

## Axiom List (6 total)
1. `exists_volume_form_of_submodule_axiom` — Volume forms exist
2. `radial_minimization` — Radial projection minimizes
3. `dist_cone_sq_formula` — Distance formula to cones

## HOW TO PROVE

See current partial proof in file — needs completion of the real dimension calculation.

---

# 🟢 AGENT 8: Type Decomposition

## Files Owned
- `Hodge/Kahler/TypeDecomposition.lean`

## Mission
Prove the 3 type decomposition axioms.

## Axiom List (3 total)
1. `ofForm_wedge_TD` — Wedge descends to cohomology
2. `omega_pow_is_p_p` — ω^p is a (p,p)-form
3. `omega_pow_IsFormClosed` — ω^p is closed
4. `omega_pow_is_rational_TD` — ω^p is rational

## HOW TO PROVE

### omega_pow_IsFormClosed
Induction on p:
```lean
theorem omega_pow_IsFormClosed (p : ℕ) : IsFormClosed (kahlerPow p) := by
  induction p with
  | zero => exact isFormClosed_one  -- or isFormClosed_zero depending on def
  | succ p ih => 
    -- kahlerPow (p+1) = ω ⋏ kahlerPow p
    exact isFormClosed_wedge K.omega_form (kahlerPow p) K.omega_closed ih
```

---

## 📈 PROGRESS TRACKING

| Agent | File(s) | Axioms | Status |
|-------|---------|--------|--------|
| 1 | Norms.lean | 6 | 🔴 FIXING BUILD |
| 2 | Lefschetz.lean | 1 | 🔴 FIXING BUILD |
| 3 | Cohomology/Basic.lean | 15 | 🟡 IN PROGRESS |
| 4 | Forms.lean | 11 | 🟡 IN PROGRESS |
| 5 | Basic.lean | 4 | 🟡 IN PROGRESS |
| 6 | Kahler/Manifolds.lean | 6 | 🟡 IN PROGRESS |
| 7 | Grassmannian.lean | 6 | 🟢 READY |
| 8 | TypeDecomposition.lean | 3 | 🟢 READY |

---

## 📝 COMPLETE AXIOM LIST (95 Total)

### Hodge/Cohomology/Basic.lean (15)
```lean
axiom cohomologous_symm
axiom cohomologous_trans
axiom instAddDeRhamCohomologyClass
axiom instNegDeRhamCohomologyClass
axiom instSubDeRhamCohomologyClass
axiom instAddCommGroupDeRhamCohomologyClass
axiom instSMulComplexDeRhamCohomologyClass
axiom instModuleComplexDeRhamCohomologyClass
axiom instSMulRationalDeRhamCohomologyClass
axiom instHMulDeRhamCohomologyClass
axiom isRationalClass_sub
axiom isRationalClass_mul
axiom mul_add, add_mul, mul_smul, smul_mul, zero_mul, mul_zero
axiom ofForm_add, ofForm_smul, ofForm_smul_real, ofForm_sub, ofForm_wedge
axiom lefschetzL_add, lefschetzL_smul
```

### Hodge/Analytic/Forms.lean (11)
```lean
axiom SmoothForm.instTopologicalSpace
axiom extDerivLinearMap
axiom isFormClosed_wedge
axiom smoothExtDeriv_extDeriv
axiom smoothExtDeriv_wedge
axiom smoothWedge_add_left, smoothWedge_add_right
axiom smoothWedge_smul_left, smoothWedge_smul_right
axiom smoothWedge_zero_left, smoothWedge_zero_right
```

### Hodge/Kahler/Manifolds.lean (6 + related)
```lean
axiom kahlerMetric_symm
axiom lefschetzLambdaLinearMap
axiom lefschetz_commutator
axiom hodgeStar_add, hodgeStar_smul_real, hodgeStar_neg, hodgeStar_sub, hodgeStar_hodgeStar
axiom adjointDeriv_add, adjointDeriv_smul_real, adjointDeriv_neg, adjointDeriv_sub, adjointDeriv_squared
axiom laplacian_add, laplacian_smul_real, laplacian_neg, laplacian_sub
axiom isHarmonic_neg, isHarmonic_add, isHarmonic_smul_real, isHarmonic_sub
axiom isHarmonic_implies_closed, isHarmonic_implies_coclosed
```

### Hodge/Analytic/Norms.lean (6)
```lean
axiom pointwiseComass_set_nonempty
axiom pointwiseComass_set_bddAbove
axiom pointwiseComass_zero
axiom pointwiseComass_smul
axiom energy_minimizer
axiom trace_L2_control
```

### Hodge/Basic.lean (4)
```lean
axiom exists_not_isClosed_set
axiom instNormTangentSpace
axiom instNormedAddCommGroupTangentSpace
axiom instNormedSpaceTangentSpace
```

### Other Files (53)
See `grep -rn "^axiom" Hodge/ --include="*.lean"` for complete list.

---

## 🎯 GOALS

### Phase 5.1 (Immediate)
- [ ] Fix Norms.lean build errors
- [ ] Fix Lefschetz.lean build errors

### Phase 5.2 (This Week)
- [ ] Reduce axioms from 95 to 60

### Phase 5.3 (Target)
- [ ] Reduce to "13 Classical Pillars" + infrastructure axioms (~30 total)
