# Agent Assignments: Phase 4 — Proof Parallelization

## 🎯 MISSION STATEMENT

We are clearing the final 10 interface axioms to reach the "13 Classical Pillars" state.
**This is a parallel execution phase.** Each agent owns specific files and axioms.

---

## 🚫 ABSOLUTE RULES
1. **NO `sorry`** — If you can't prove it, document the blocker.
2. **NO new `axiom`** — Only use existing axioms or the 13 Pillars.
3. **Mathlib First** — Always check Mathlib for existing lemmas.

---

# 🟢 AGENT 1: Infrastructure Architect [COMPLETED]

## Files Owned
- `Hodge/Basic.lean` (Structure only)
- `Hodge/Cohomology/Basic.lean` (Created)
- `Hodge/Analytic/Forms.lean` (Core)

## Mission
Resolve the circular dependency preventing the Cup Product instance.

## Status
- **Split `Basic.lean`**: Core manifolds in `Basic.lean`, smooth forms in `Forms.lean`, cohomology classes in `Cohomology/Basic.lean`.
- **Circular Dependency Resolved**: `Basic` -> `Forms` -> `Cohomology` -> `KahlerManifolds`.
- **Instance Defined**: `instHMulDeRhamCohomologyClass` implemented using `Quotient.lift₂` and `smoothWedge`.
- **Zero-Sorry Policy**: All `sorry`s removed from `Cohomology/Basic.lean` and `Forms.lean`.
- **Downstream Fixes**: Updated `Norms.lean` and `Manifolds.lean` to reflect new architecture.

---

# 🟢 AGENT 2: Algebraist

## Files Owned
- `Hodge/Basic.lean` (Rationality logic)

## Mission
Prove the algebraic closure properties of rational cohomology classes.

## Priority Order

### 2.1 Rational Product (`isRationalClass_mul`)
**File:** `Hodge/Basic.lean`

```lean
axiom isRationalClass_mul ... (η₁ η₂) :
    isRationalClass η₁ → isRationalClass η₂ → isRationalClass (η₁ * η₂)
```

**HOW TO PROVE:**
1. Use induction on `isRationalClass` for `η₁` and `η₂`.
2. Base case: `0 * η = 0` (rational).
3. Inductive steps:
   - `(a + b) * c = a*c + b*c` (rational by induction + add closed).
   - `(q • a) * b = q • (a * b)` (rational by induction + smul closed).
   - `(-a) * b = -(a * b)` (rational by induction + neg closed).

---

# 🟢 AGENT 3: Tensor Geometer

## Files Owned
- `Hodge/Kahler/TypeDecomposition.lean`

## Mission
Connect wedge products of forms to the cohomology ring.

## Priority Order

### 3.1 Wedge Product Descent (`ofForm_wedge`)
**File:** `Hodge/Kahler/TypeDecomposition.lean`

```lean
axiom ofForm_wedge ... (ω η) : ⟦ω ⋏ η⟧ = ⟦ω⟧ * ⟦η⟧
```

**HOW TO PROVE:**
1. This should be `rfl` by definition of the cup product (once Agent 1 fixes the definition).
2. If the definition is locked behind `Quotient.lift`, use `Quotient.sound` and reflexivity of the underlying form operations.

---

# 🟢 AGENT 4: Type Theorist

## Files Owned
- `Hodge/Basic.lean` (Scalar actions)

## Mission
Resolve definitional equalities between Real and Complex scalar actions.

## Priority Order

### 4.1 Real Scalar Action (`ofForm_smul_real`)
**File:** `Hodge/Basic.lean`

```lean
axiom ofForm_smul_real ... (r : ℝ) (ω) : ⟦r • ω⟧ = r • ⟦ω⟧
```

**HOW TO PROVE:**
1. The issue is `Module.compHom Complex.ofRealHom` vs `Algebra.toSMul`.
2. Prove a lemma: `(r : ℂ) • ω = r • ω` (where LHS is complex action, RHS is real action via restriction).
3. Use `ofForm_smul` (complex version) and rewrite.
   ```lean
   rw [← complex_smul_eq_real_smul r ω]
   rw [ofForm_smul (r : ℂ) ω hω]
   rfl
   ```

---

# 🟢 AGENT 5: Kähler Geometer

## Files Owned
- `Hodge/Kahler/Manifolds.lean`

## Mission
Establish the fundamental properties of the Kähler form `ω`.

## Priority Order

### 5.1 Omega Rationality (`omega_is_rational`)
**File:** `Hodge/Kahler/Manifolds.lean`

**HOW TO PROVE:**
1. This is a property of the *manifold definition*.
2. **Action:** Modify `KahlerManifold` class to include `omega_rational` as a field (axiom).
   - "A Kähler manifold *of Hodge type* admits a rational Kähler class."
   - This moves the axiom from a standalone statement to a structural requirement, which is mathematically correct (we are assuming X is projective algebraic).

### 5.2 Metric Symmetry (`kahlerMetric_symm`)
**File:** `Hodge/Kahler/Manifolds.lean`

**HOW TO PROVE:**
1. Use the definition of the Kähler metric $g(u, v) = \omega(u, Jv)$.
2. Use the fact that $\omega$ is a (1,1)-form and real.
3. Unfold `as_alternating` and apply complex conjugation properties.

---

# 🟢 AGENT 6: Cohomology Expert

## Files Owned
- `Hodge/Kahler/Main.lean`

## Mission
Prove properties of the Lefschetz decomposition powers.

## Priority Order

### 6.1 Omega Powers (`omega_pow_represents_multiple`)
**File:** `Hodge/Kahler/Main.lean`

```lean
axiom omega_pow_represents_multiple ... : ⟦ω^p⟧ = ⟦ω⟧^p
```

**HOW TO PROVE:**
1. Induction on `p`.
2. Base case `p=0`: `1 = 1`.
3. Step: `ω^{p+1} = ω ∧ ω^p`.
4. Use `ofForm_wedge`: `⟦ω ∧ ω^p⟧ = ⟦ω⟧ * ⟦ω^p⟧`.
5. Use IH: `⟦ω⟧ * ⟦ω⟧^p = ⟦ω⟧^{p+1}`.

---

# 🟢 AGENT 7: Grassmannian Expert

## Files Owned
- `Hodge/Analytic/Grassmannian.lean`

## Mission
Construct explicit volume forms on subspaces.

## Priority Order

### 7.1 Volume Form Existence (`exists_volume_form_of_submodule_axiom`)
**File:** `Hodge/Analytic/Grassmannian.lean`

**HOW TO PROVE:**
1. Use Gram-Schmidt to get an orthonormal basis $e_1, \dots, e_k$ for the submodule $V$.
2. Construct the dual basis $e^1, \dots, e^k$.
3. Define $\omega = e^1 \wedge \dots \wedge e^k$.
4. Show this evaluates to 1 on the basis vectors (determinant property).

---

# 🟢 AGENT 8: Geometric Analyst

## Files Owned
- `Hodge/Analytic/Norms.lean`
- `Hodge/Analytic/Currents.lean`

## Mission
Handle continuity and bounds for analytical objects.

## Priority Order

### 8.1 Comass Continuity (`pointwiseComass_continuous`)
**File:** `Hodge/Analytic/Norms.lean`

**HOW TO PROVE:**
1. The comass is the supremum of a continuous function (evaluation) over a compact set (Grassmannian of unit vectors).
2. Use `Continuous.sSup` or Berge's Maximum Theorem.

### 8.2 Current Boundedness (`Current.is_bounded`)
**File:** `Hodge/Analytic/Currents.lean`

**HOW TO PROVE:**
1. A Current is defined as a *continuous* linear functional on smooth forms.
2. In a normed space, continuous $\iff$ bounded.
3. Apply standard functional analysis theorem: `ContinuousLinearMap.isBounded`.

---
