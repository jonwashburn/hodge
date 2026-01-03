# Agent Assignments: Phase 3 — Proving Interface Axioms

## Current Status (Just Pushed!)

| Metric | Value |
|--------|-------|
| **Proof Chain Axioms** | **17** custom axioms |
| **Lean Foundations** | 3 (propext, Classical.choice, Quot.sound) |
| **Classical Pillars** | 7 (keep as axioms) |
| **Interface Axioms** | 10 (to prove) |
| **Opaques** | 0 ✅ |
| **Build** | ✅ Passing |

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

## 🎯 Interface Axioms to Prove (10 remaining)

### Cohomology Structure (4)
| # | Axiom | File | Difficulty |
|---|-------|------|------------|
| 1 | `instHMulDeRhamCohomologyClass` | Basic.lean | 🔴 Hard (circular deps) |
| 2 | `isRationalClass_mul` | Basic.lean | 🟡 Medium |
| 3 | `ofForm_transport` | TypeDecomposition.lean | 🟢 Easy |
| 4 | `ofForm_wedge` | TypeDecomposition.lean | 🟡 Medium |

### Scalar Multiplication (2)
| # | Axiom | File | Difficulty |
|---|-------|------|------------|
| 5 | `ofForm_smul_real` | Basic.lean | 🔴 Hard (definitional mismatch) |
| 6 | `omega_is_rational` | Manifolds.lean | 🔴 Hard (needs axiom on class) |

### Representation (1)
| # | Axiom | File | Difficulty |
|---|-------|------|------------|
| 7 | `omega_pow_represents_multiple` | Main.lean | 🟡 Medium |

### Technical (3)
| # | Axiom | File | Difficulty |
|---|-------|------|------------|
| 8 | `exists_volume_form_of_submodule_axiom` | Grassmannian.lean | 🟡 Medium |
| 9 | `pointwiseComass_continuous` | Norms.lean | 🟡 Medium |
| 10 | `Current.is_bounded` | Currents.lean | 🟢 Easy |

---

## ALL 8 AGENTS: Work on `ofForm_transport`

**This is the EASIEST axiom to prove!**

**File:** `Hodge/Kahler/TypeDecomposition.lean`

```lean
axiom ofForm_transport {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) (hω : IsFormClosed ω)
    (hcast : IsFormClosed (h ▸ ω)) :
    ⟦h ▸ ω, hcast⟧ = h ▸ ⟦ω, hω⟧
```

**Strategy:**
1. Use `subst h` to eliminate the equality
2. After subst, both sides should be definitionally equal
3. Apply `ofForm_proof_irrel` or `rfl`

**Proof sketch:**
```lean
theorem ofForm_transport {k l : ℕ} (h : k = l) (ω : SmoothForm n X k) (hω : IsFormClosed ω)
    (hcast : IsFormClosed (h ▸ ω)) :
    ⟦h ▸ ω, hcast⟧ = h ▸ ⟦ω, hω⟧ := by
  subst h
  exact ofForm_proof_irrel ω hcast hω
```

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

---

## Summary

**We're making progress!** The proof chain is down to 17 custom axioms from the original ~100+.

The 7 classical pillars will remain as axioms (they represent deep theorems from the literature).

The remaining 10 interface axioms are targets for all 8 agents to prove.
