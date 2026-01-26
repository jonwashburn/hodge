# Unconditional Hodge Conjecture Proof Plan

## ⚠️ GOAL: COMPLETE FORMALIZATION - NO SEMANTIC STUBS

**The goal is to formalize EVERYTHING:**
- Every `sorry` must be eliminated
- Every semantic stub (`:= 0`, `True := trivial`) must be replaced with real content
- All GMT theorems must be fully formalized
- NO SHORTCUTS. NO PLACEHOLDERS. FULL MATHEMATICAL CONTENT.

---

## Current Status (2026-01-26, Session 2)

### Progress
| Metric | Session Start | Current | Reduction |
|--------|---------------|---------|-----------|
| Sorries | 9 | 8 | 11% |

### Kernel Status
```
'hodge_conjecture' depends on axioms: [propext, Classical.choice, Quot.sound]
'hodge_conjecture'' depends on axioms: [propext, Classical.choice, Quot.sound]
```
✅ **KERNEL-CLEAN** - Only standard Lean axioms

---

## Remaining Sorries (8)

### Hodge/Analytic/Currents.lean (4 sorries)
| Line | Theorem | Mathematical Content |
|------|---------|---------------------|
| 692 | `hausdorffIntegrate_linear` | Bochner integral linearity |
| 708 | `hausdorffIntegrate_bound` | Mass-comass inequality |
| 878 | stokes_bound (rectifiable) | Stokes theorem for rectifiable sets |
| 905 | stokes_bound (closed) | Stokes theorem (trivial: ∂Z = ∅) |

### Hodge/Kahler/Microstructure.lean (3 sorries)
| Line | Theorem | Mathematical Content |
|------|---------|---------------------|
| 199 | RawSheetSum stokes_bound | Uses Currents.lean stokes |
| 244 | is_integral | Federer-Fleming integrality |
| 458 | mass_bound | Uses hausdorffIntegrate_bound |

### Hodge/Classical/HarveyLawson.lean (1 sorry)
| Line | Theorem | Mathematical Content |
|------|---------|---------------------|
| 214 | represents_input | Core Harvey-Lawson theorem |

---

## This Session's Progress

### Theorems Proved
1. **`formVectorPairing_add`** - Pairing is additive: `⟨ω₁+ω₂, τ⟩ = ⟨ω₁,τ⟩ + ⟨ω₂,τ⟩`
2. **`formVectorPairing_smul`** - Pairing is scalar-multiplicative: `⟨c•ω, τ⟩ = c·⟨ω,τ⟩`
3. **`integrate_linear` refactored** - Now uses `hausdorffIntegrate_linear` (2 sorries consolidated into 1)

### Key Structural Fixes
- Fixed scalar type in `hausdorffIntegrate_linear` (was ℂ, should be ℝ)
- Added helper lemmas for formVectorPairing linearity
- Consolidated duplicate integrate_linear sorries

---

## Mathematical Dependency Tree

```
hausdorffIntegrate_linear (Bochner integral linearity)
    └── integrate_linear (Rectifiable) - USES THIS
    └── integrate_linear (Closed) - USES THIS

hausdorffIntegrate_bound (Mass-comass inequality)
    └── integrate_bound (Rectifiable) - USES THIS
    └── integrate_bound (Closed) - USES THIS
    └── mass_bound in Microstructure - USES THIS

stokes_bound (Stokes theorem)
    └── For closed: ∫_Z dω = 0 since ∂Z = ∅
    └── For rectifiable: |∫_Z dω| ≤ mass(∂Z) · ‖ω‖
    └── Microstructure stokes_bound - USES THIS

is_integral (Federer-Fleming)
    └── Integration currents are integral
    
represents_input (Harvey-Lawson)
    └── Witness current represents input class
```

---

## Core Theorems Needed

### 1. Bochner Integral Linearity (hausdorffIntegrate_linear)
**Goal**: `∫_Z (c•ω₁ + ω₂) = c · ∫_Z ω₁ + ∫_Z ω₂`

**Proof sketch**:
```lean
simp only [hausdorffIntegrate, formVectorPairing]
simp only [SmoothForm.add_apply, SmoothForm.smul_real_apply]
simp only [ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply]
-- Now need: (∫ x, c • f x + g x ∂μ).re = c * (∫ f).re + (∫ g).re
-- Requires: MeasureTheory.integral_add, integral_smul, Complex.add_re
```

**Mathlib lemmas needed**:
- `MeasureTheory.integral_add`
- `MeasureTheory.integral_smul`
- Integrability conditions

### 2. Mass-Comass Inequality (hausdorffIntegrate_bound)
**Goal**: `|∫_Z ω| ≤ mass(Z) · comass(ω)`

**Proof**:
1. `|∫_Z ω| = |∫ x, ⟨ω(x), τ(x)⟩ dH^k|.re|`
2. `≤ |∫ x, ⟨ω(x), τ(x)⟩ dH^k|` (abs_re_le_abs)
3. `≤ ∫ x, |⟨ω(x), τ(x)⟩| dH^k` (norm_integral_le)
4. `≤ ∫ x, comass(ω) dH^k` (definition of comass)
5. `= comass(ω) · H^k(Z) = comass(ω) · mass(Z)`

### 3. Stokes' Theorem
**For closed (∂Z = ∅)**: `∫_Z dω = 0`
**For rectifiable**: `|∫_Z dω| ≤ mass(∂Z) · ‖ω‖`

### 4. Federer-Fleming Integrality
Integration currents over compact submanifolds are integral currents.

### 5. Harvey-Lawson Witness
The witness current represents the input Hodge class.

---

## Agent Strategy

### What Works
- Targeted agents with specific lemma context
- Proving one sorry at a time
- Providing exact Mathlib lemma names

### What Doesn't Work
- Agents that can modify definitions (they just make things := 0)
- Large file replacements
- Vague task descriptions

### Recommended Approach
1. **Local manual work** for complex proofs
2. **Agents** for finding Mathlib lemmas and syntax
3. **Sync and verify** after each change

---

## Files Modified This Session

1. `Hodge/Analytic/Currents.lean`
   - Added `formVectorPairing_add`, `formVectorPairing_smul`
   - Fixed `hausdorffIntegrate_linear` scalar type
   - Consolidated integrate_linear sorries

---

## Commits

- Previous session: Reduced 29 → 9 sorries
- This session: Reduced 9 → 8 sorries (structural improvements)
