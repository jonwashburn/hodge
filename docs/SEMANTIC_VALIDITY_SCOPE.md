# Hodge Conjecture Formalization: Semantic Validity Scope

## Overview

This document clarifies which parts of the formalization carry full mathematical
content versus structural scaffolding.

## Axiom Status (proof-term axioms)

**Current status (as of 2026-01-09):**
- ✅ **No project-level `axiom` declarations** in `Hodge/` on the main build path
- ✅ Only standard Lean foundation axioms appear in `#print axioms` (e.g. `propext`, `Classical.choice`, `Quot.sound`)
- ✅ `opaque` declarations are eliminated in `Hodge/`

**Important caveat**: “No axioms in the proof term” is **not** the same as Clay-standard.
The development still contains **semantic stubs** (degenerate definitions like `d := 0`)
that make many statements provable for the wrong reason. The referee remediation plan
(`docs/referee/Hodge_REFEREE_Amir-v1b_ISSUES_AND_REMEDIATION_PLAN.md`) treats these as
Clay-critical.

## What is *actually* semantically faithful today?

### Proven (within the current `SmoothForm`/`FiberAlt` model)
- **Fiberwise wedge product** (`Hodge/Analytic/DomCoprod.lean`): a real construction of
  `ContinuousAlternatingMap.wedge` and its linearity properties.
- **Model-space exterior derivative** (`Hodge/Analytic/ModelDeRham.lean`): `ModelForm.d` is defined
  using Mathlib’s `extDeriv` on the model space `ℂⁿ` (this is *not* yet integrated into the main path).

## Critical semantic stubs (affecting the main theorem path)

These are the main “degenerate model” points referenced by Section **E** of the referee plan.

### Exterior derivative stub (`Hodge/Analytic/Forms.lean`)
- `extDerivLinearMap := 0`, hence `smoothExtDeriv = 0`
- **Impact**: “closed/exact” and de Rham cohomology are not the intended mathematics yet.

### Fundamental class stub (`Hodge/Classical/GAGA.lean`)
- `FundamentalClassSet_impl := 0` (cycle class map returns the zero form)
- **Impact**: algebraic-cycle → cohomology comparisons are presently vacuous.

### Current/integration stubs (`Hodge/Analytic/Currents.lean`)
- `integration_current := 0` (definitional stub)
- **Impact**: the measure-theoretic integration/current pairing is not implemented yet.

### Rationality stub (`Hodge/Cohomology/Basic.lean`)
- `isRationalClass` is an inductive closure with base case `zero`
- **Impact**: many “rationality” arguments collapse to “everything rational is 0”.

### Hodge-type stub (`Hodge/Cohomology/Basic.lean`)
- `isPPForm'` has only the base constructor `zero` plus closure operations
- **Impact**: any form satisfying `isPPForm'` is forced to be `0` (used to deduce `omega_form = 0`).

### Unit element stub (`Hodge/Analytic/Forms.lean`)
`unitForm` is now implemented as the constant-`1` 0-form.

**Remaining gap**: the cohomology-ring unit laws should eventually be re-proved against a real exterior
derivative / real de Rham quotient (not `smoothExtDeriv := 0`).

## Known Stubs (Not Affecting Main Theorem)

### Kähler Operators (Intentionally Stubbed)
These are stubbed as `0` because they're not used in the main theorem path:

```lean
lefschetzLambdaLinearMap := 0  -- dual Lefschetz Λ
hodgeStar := 0                  -- Hodge star ⋆
adjointDeriv := 0               -- codifferential δ
laplacian := 0                  -- Hodge Laplacian Δ
```

**Impact**: None on main theorem. These would be needed for Hodge theory,
which is orthogonal to the algebraic cycle representation proof.

### Inner Product (Stubbed)
```lean
pointwiseInner := 0
L2Inner := 0
```

**Impact**: None on main theorem. Used only for energy minimization proofs.

### `kahlerPow`
`kahlerPow` is now defined **recursively using the actual wedge product** (with a degree cast),
so it no longer degenerates to `0` by definition for `p ≥ 2`.

**Remaining stub**: ω^0 is still represented using the placeholder `unitForm := 0`.

## Sorry Blocks

### Advanced/LeibnizRule.lean (2 sorry)
- `alternatizeUncurryFin_wedge_right`: Combinatorial identity about domCoprod
- `alternatizeUncurryFin_wedge_left`: Same with graded sign

**Impact**: These are in the isolated `Advanced/` module (not imported by main theorem).
The Leibniz rule infrastructure is for future development, not the current proof.

### Advanced/ContMDiffForms.lean (comments mentioning sorry)
These are documentation comments, not actual sorry usage in proofs.

## Semantic Validity Assessment

### Main theorem status (`hodge_conjecture`)
The theorem statement type-checks and builds, but **the current proof is not Clay-standard**
because it depends on the semantic stubs listed above (in particular `d := 0` and
`FundamentalClassSet := 0`).

This repo is explicitly in a staged “proof-first” mode; the referee remediation plan documents
the work needed to replace these stubs with real mathematics.

### What "Clay Standards" Would Require
1. **Kähler operators**: Replace stubs with real definitions using Riemannian metrics
2. **Leibniz rule**: Complete the domCoprod combinatorics
3. **Integration**: Formalize measure-theoretic integration on manifolds
4. **Algebraic geometry**: Connect to Mathlib's scheme theory when available

## Verification Commands

```bash
# Run the audit script
./scripts/audit_stubs.sh

# Check for non-standard axioms
lake env lean Hodge/Utils/AuditAxioms.lean

# Build verification
lake build Hodge
```

## Last Updated
2026-01-09

## Authors
Jonathan Washburn, AI Assistants

