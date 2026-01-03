# Agent Assignments: Phase 2 Progress

## 🎉 ALL OPAQUES ELIMINATED!

**15 opaques → 0 opaques** — All converted to concrete definitions!

---

## Current Status

| Metric | Previous | Current |
|--------|----------|---------|
| Opaques | 15 | **0** ✅ |
| Total axioms | ~63 | **~57** |
| Proved this round | — | **6** |
| Classical pillars | 6 | 6 |

---

## ✅ PROVED THIS ROUND

| Axiom | Agent |
|-------|-------|
| `smoothWedge_add_left` | 2 |
| `smoothWedge_add_right` | 2 |
| `smoothWedge_smul_left` | 2 |
| `smoothWedge_smul_right` | 2 |
| `isFormClosed_wedge` | 2 |
| + 1 more | — |

---

## Rebalanced Assignments

### 🔷 AGENT 1: Exterior Derivative (3 axioms)

**File:** `Hodge/Basic.lean`

| Axiom | Strategy |
|-------|----------|
| `smoothExtDeriv_add` | Linearity |
| `smoothExtDeriv_smul` | Linearity |
| `smoothExtDeriv_wedge` | Product rule |

---

### 🔷 AGENT 2: ✅ DONE — New Assignment: Lefschetz

**Previous:** Wedge axioms (5/7 proved, 2 blocked by HEq)

**New File:** `Hodge/Analytic/Forms.lean`, `Hodge/Classical/Lefschetz.lean`

| Axiom | Strategy |
|-------|----------|
| `lefschetzL_add` | Linearity |
| `lefschetzLambda_add` | Linearity |
| `lefschetz_commutator` | [L, Λ] = (n-k)·id |

---

### 🔷 AGENT 3: Hodge Star (3 axioms)

**File:** `Hodge/Analytic/Forms.lean`

| Axiom | Strategy |
|-------|----------|
| `hodgeStar_hodgeStar` | ⋆⋆ω = ±ω |
| `hodgeStar_add` | Linearity |
| `hodgeStar_smul_real` | Linearity |

---

### 🔷 AGENT 4: Adjoint & Laplacian (7 axioms)

**File:** `Hodge/Analytic/Forms.lean`

| Axiom | Strategy |
|-------|----------|
| `adjointDeriv_add` | Linearity |
| `adjointDeriv_smul_real` | Linearity |
| `adjointDeriv_squared` | δ² = 0 |
| `laplacian_add` | Linearity |
| `laplacian_smul_real` | Linearity |
| `isHarmonic_implies_closed` | Δω=0 → dω=0 |
| `isHarmonic_implies_coclosed` | Δω=0 → δω=0 |

---

### 🔷 AGENT 5: Norm Axioms (5 axioms)

**File:** `Hodge/Analytic/Norms.lean`

| Axiom | Strategy |
|-------|----------|
| `pointwiseComass_nonneg` | Norm ≥ 0 |
| `pointwiseComass_zero` | Norm of 0 = 0 |
| `pointwiseComass_add_le` | Triangle inequality |
| `pointwiseComass_smul` | Homogeneity |
| `comass_eq_zero_iff` | Norm = 0 ↔ ω = 0 |

---

### 🔷 AGENT 6: Inner Product (7 axioms)

**File:** `Hodge/Analytic/Norms.lean`

| Axiom | Strategy |
|-------|----------|
| `pointwiseInner_comm` | Symmetry |
| `pointwiseInner_self_nonneg` | ⟨ω,ω⟩ ≥ 0 |
| `L2Inner_add_left` | Linearity |
| `L2Inner_smul_left` | Linearity |
| `L2Inner_comm` | Symmetry |
| `L2Inner_self_nonneg` | ⟨ω,ω⟩ ≥ 0 |
| `L2Inner_cauchy_schwarz` | Cauchy-Schwarz |

---

### 🔷 AGENT 7: Grassmannian & Cone (5 axioms)

**File:** `Hodge/Analytic/Grassmannian.lean`, `Hodge/Kahler/Cone.lean`

| Axiom | Strategy |
|-------|----------|
| `distToCone_nonneg` | Distance ≥ 0 |
| `coneDefect_nonneg` | Supremum of nonneg |
| `dist_cone_sq_formula` | From definition |
| `omegaPow_in_interior` | Wirtinger-based |
| `exists_uniform_interior_radius` | Compactness |

---

### 🔷 AGENT 8: Critical Path + Classical Pillars (8 axioms)

**Files:** Various

**Hodge-Weight (investigate):**
| Axiom | File |
|-------|------|
| `omega_pow_represents_multiple` | Main.lean |
| `wirtinger_comass_bound` | Calibration.lean |
| `hard_lefschetz_bijective` | Lefschetz.lean |

**Classical Pillars (document, keep as axioms):**
| Axiom | Reference |
|-------|-----------|
| `serre_gaga` | Serre 1956 |
| `flat_limit_existence` | FF 1960 |
| `mass_lsc` | Federer 1969 |
| `calibration_defect_from_gluing` | FF 1960 |
| `harvey_lawson_fundamental_class` | HL 1983 |
| `lefschetz_lift_signed_cycle` | Hard Lefschetz |

---

## Blocked Axioms (HEq Complexity)

These require heterogeneous equality across form degrees:

| Axiom | Issue |
|-------|-------|
| `smoothWedge_assoc` | `(k+l)+m = k+(l+m)` type coercion |
| `smoothWedge_comm` | `k+l = l+k` type coercion |

**Strategy:** May need `cast` or `HEq` machinery, or accept as structural axioms.

---

## Summary

| Agent | Axioms | Focus |
|-------|--------|-------|
| 1 | 3 | Exterior derivative |
| 2 | 3 | Lefschetz operators |
| 3 | 3 | Hodge star |
| 4 | 7 | Adjoint & Laplacian |
| 5 | 5 | Norms |
| 6 | 7 | Inner products |
| 7 | 5 | Grassmannian & cone |
| 8 | 8 | Critical path + pillars |

**Total assigned:** ~41 axioms  
**Remaining after this round:** ~16 axioms  
**Target:** 6 classical pillars + ~2-4 HEq-blocked

---

## Verification

```bash
# Count axioms
grep -rh "^axiom " Hodge/ --include="*.lean" | wc -l

# Build test
lake build Hodge
```
