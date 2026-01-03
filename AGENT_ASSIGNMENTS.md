# Agent Assignments: Phase 3 — Proving Interface Axioms

## Current Status

| Metric | Value |
|--------|-------|
| **Proof Chain Axioms** | **17** custom axioms |
| **Lean Foundations** | 3 (propext, Classical.choice, Quot.sound) |
| **Classical Pillars** | 7 (keep as axioms) |
| **Interface Axioms** | 7 (to prove) |
| **Opaques** | 0 ✅ |

---

## ✅ Just Proved!

| Axiom | File | Status |
|-------|------|--------|
| `unitForm_isClosed` | Manifolds.lean | ✅ **Theorem** |
| `unitForm_is_rational` | Manifolds.lean | ✅ **Theorem** |

---

## 🏛️ Classical Pillars (7 Axioms - Keep)

These are deep published theorems intentionally kept as axioms:

| # | Axiom | File | Reference |
|---|-------|------|-----------|
| 1 | `serre_gaga` | GAGA.lean | Serre 1956 |
| 2 | `flat_limit_existence` | Microstructure.lean | Federer-Fleming 1960 |
| 3 | `mass_lsc` | Calibration.lean | Federer 1969 |
| 4 | `calibration_defect_from_gluing` | Microstructure.lean | Federer-Fleming 1960 |
| 5 | `harvey_lawson_fundamental_class` | Main.lean | Harvey-Lawson 1982 |
| 6 | `lefschetz_lift_signed_cycle` | Main.lean | Hard Lefschetz |
| 7 | `exists_uniform_interior_radius` | Cone.lean | Compactness |

---

## 🎯 Interface Axioms to Prove (7 remaining)

| # | Axiom | File | Strategy |
|---|-------|------|----------|
| 1 | `instHMulDeRhamCohomologyClass` | Basic.lean | Needs refactoring to avoid circular deps |
| 2 | `isRationalClass_mul` | Basic.lean | Follows from cup product definition |
| 3 | `ofForm_smul_real` | Basic.lean | Module compatibility |
| 4 | `ofForm_transport` | TypeDecomposition.lean | Type transport proof |
| 5 | `ofForm_wedge` | TypeDecomposition.lean | Cup product compatibility |
| 6 | `omega_is_rational` | Manifolds.lean | Requires rationality axiom on KahlerManifold |
| 7 | `omega_pow_represents_multiple` | Main.lean | Cohomology representation |

Plus 3 additional interface axioms:
- `exists_volume_form_of_submodule_axiom` - Grassmannian.lean
- `pointwiseComass_continuous` - Norms.lean  
- `Current.is_bounded` - Currents.lean

---

## ALL 8 AGENTS: Focus on Single Easiest Axiom

**Target: `ofForm_smul_real`**

This axiom states:
```lean
axiom ofForm_smul_real {k : ℕ} (r : ℝ) (ω : SmoothForm n X k) (hω : IsFormClosed ω) :
    ⟦r • ω, isFormClosed_smul_real hω⟧ = r • ⟦ω, hω⟧
```

**Why this is provable:**
- Scalar multiplication by `r : ℝ` is defined on both forms and cohomology classes
- The quotient should respect this structure
- This is essentially `rfl` if the definitions are compatible

**All 8 agents should attempt to prove this axiom in Basic.lean**

---

## Verification

```bash
# Count remaining axioms in proof chain
lake env lean DependencyCheck.lean 2>&1 | grep -v "error" | tail -25

# Count total axioms
grep -rn "^\s*axiom " Hodge/ --include="*.lean" | wc -l

# Build
lake build Hodge
```
