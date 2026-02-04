# Hodge Conjecture Lean 4 Formalization - Release Checklist

**Version**: 1.0.0-rc1  
**Date**: 2026-01-21  
**Lean Version**: v4.27.0-rc1  
**Mathlib Version**: v4.27.0 (from lake-manifest.json)

---

## Overview

This document provides a comprehensive checklist for verifying the Hodge Conjecture
formalization before release. All items must pass before tagging a release.

---

## 1. Build Verification

### 1.1 Mathlib Cache

```bash
# Always get cache before building (saves 2-4 hours)
lake exe cache get
```

- [ ] Cache downloaded successfully
- [ ] No network errors during cache retrieval

### 1.2 Full Build

```bash
./scripts/build.sh
# Or manually:
lake exe cache get && lake build
```

- [ ] Build completes without errors
- [ ] All 3046+ jobs complete successfully
- [ ] No unexpected warnings

### 1.3 Specific Module Builds

```bash
lake build Hodge.Kahler.Main
lake build Hodge.Tests.MasterTests
lake build Hodge.GMT.GMTTests
```

- [ ] Main theorem module builds
- [ ] Test modules build
- [ ] GMT test module builds

---

## 2. Axiom Verification

### 2.1 Main Theorem Axioms

```bash
lake env lean Hodge/Utils/DependencyCheck.lean
```

**Expected output:**
```
Axioms used by hodge_conjecture_data:
  - propext
  - Classical.choice
  - Quot.sound
```

- [ ] Only standard Lean/Mathlib axioms appear
- [ ] No custom `axiom` declarations in output
- [ ] No unexpected dependencies

### 2.2 Audit Script

```bash
./scripts/audit_stubs.sh --full
```

- [ ] No "Critical" issues reported
- [ ] Quarantined sorries remain at 2 (documented interface assumptions)
- [ ] No new `sorry` statements on proof track

### 2.3 Sorry Count

```bash
lake build 2>&1 | grep "uses 'sorry'" | wc -l
```

- [ ] Count equals 2 (the documented interface sorries)
- [ ] Sorries are in `Currents.lean` and `Microstructure.lean` only

---

## 3. Test Suite

### 3.1 Master Tests

```bash
lake build Hodge.Tests.MasterTests
```

- [ ] All examples in MasterTests.lean compile
- [ ] `topFormIntegral_real'` tests pass
- [ ] `L2InnerProduct` tests pass
- [ ] Cross-module import tests pass

### 3.2 Integration Tests

```bash
lake build Hodge.Analytic.Advanced.IntegrationTests
lake build Hodge.Analytic.Laplacian.ConnectionTests
lake build Hodge.Kahler.Lefschetz.LefschetzTests
lake build Hodge.GMT.GMTTests
```

- [ ] IntegrationTests compile
- [ ] ConnectionTests compile
- [ ] LefschetzTests compile
- [ ] GMTTests compile

### 3.3 Functional Verification

The following properties should hold (verified by examples in test files):

- [ ] `topFormIntegral_real' 0 = 0` (zero property)
- [ ] `topFormIntegral_real'` is linear
- [ ] `L2InnerProduct` is sesquilinear
- [ ] `L2InnerProduct` is Hermitian: `⟨ω, η⟩ = conj(⟨η, ω⟩)`
- [ ] `L2InnerProduct ω ω ≥ 0` (positive semidefinite)
- [ ] `integration_current` produces valid currents
- [ ] `hodgeLaplacian` is well-typed

---

## 4. Documentation Completeness

### 4.1 Core Documentation

- [ ] `README.md` - Updated with current status
- [ ] `docs/PROOF_TRACK_STATUS.md` - Axiom tracking up to date
- [ ] `docs/OPERATIONAL_PLAN_5_AGENTS.md` - All rounds documented

### 4.2 Mathematical Documentation

- [ ] Main theorem (`Hodge/Kahler/Main.lean`) has comprehensive docstrings
- [ ] Microstructure construction documented with references
- [ ] Harvey-Lawson theorem documented with references
- [ ] Key lemmas have mathematical context

### 4.3 Reference Coverage

The following papers should be cited in docstrings:

- [ ] Hodge (1950) - Original conjecture statement
- [ ] Federer-Fleming (1960) - Integral currents, compactness
- [ ] Harvey-Lawson (1982) - Calibrated geometries
- [ ] Serre (1956) - GAGA principle
- [ ] Voisin (2002) - Hodge theory textbook
- [ ] Griffiths-Harris (1978) - Algebraic geometry reference

---

## 5. Code Quality

### 5.1 No Debug Code

```bash
grep -r "dbg_trace\|#check\|#eval" Hodge/ --include="*.lean" | grep -v "^Hodge/Tests"
```

- [ ] No debug traces in production code
- [ ] `#check` and `#eval` only in test files

### 5.2 Import Hygiene

```bash
# Check for unused imports (manual review)
lake build 2>&1 | grep "unused import"
```

- [ ] No unused import warnings
- [ ] Import structure is clean

### 5.3 Naming Conventions

- [ ] Theorems use `snake_case`
- [ ] Structures use `PascalCase`
- [ ] Consistent naming across modules

---

## 6. File Structure

### 6.1 Core Files Present

```
Hodge/
├── Kahler/
│   ├── Main.lean          # Main theorem
│   ├── Microstructure.lean
│   ├── Manifolds.lean
│   └── ...
├── Classical/
│   ├── HarveyLawson.lean
│   ├── GAGA.lean
│   └── ...
├── Analytic/
│   ├── Currents.lean
│   ├── Integration/
│   └── ...
├── GMT/
│   └── ...
└── Tests/
    └── MasterTests.lean
```

- [ ] All expected directories exist
- [ ] Main theorem file exists
- [ ] Test directory has MasterTests.lean

### 6.2 Archive

```bash
ls archive/
```

- [ ] Deprecated files moved to archive/
- [ ] Archive has README explaining contents

---

## 7. Version Control

### 7.1 Clean State

```bash
git status
```

- [ ] No uncommitted changes (or all changes are intentional)
- [ ] .gitignore is up to date
- [ ] No large generated files committed

### 7.2 Branch

```bash
git branch --show-current
```

- [ ] On appropriate release branch
- [ ] All feature branches merged

---

## 8. Final Verification Commands

Run all verification in sequence:

```bash
# Full verification script
cd /path/to/hodge

# 1. Build
lake exe cache get
lake build

# 2. Axioms
lake env lean Hodge/Utils/DependencyCheck.lean

# 3. Tests
lake build Hodge.Tests.MasterTests

# 4. Audit
./scripts/audit_stubs.sh --full

# 5. Sorry count
lake build 2>&1 | grep "uses 'sorry'" | wc -l

echo "All checks complete!"
```

---

## 9. Release Tagging

Once all items above pass:

```bash
# Create annotated tag
git tag -a v1.0.0-rc1 -m "Hodge Conjecture Formalization v1.0.0-rc1

Main theorem: hodge_conjecture_data in Hodge/Kahler/Main.lean

Axioms: [propext, Classical.choice, Quot.sound] (standard Lean/Mathlib only)

Verified: 2026-01-21
Lean: v4.27.0-rc1
Mathlib: v4.27.0"

# Push tag
git push origin v1.0.0-rc1
```

---

## Checklist Summary

| Category | Items | Passing |
|----------|-------|---------|
| Build Verification | 6 | ☐ |
| Axiom Verification | 6 | ☐ |
| Test Suite | 12 | ☐ |
| Documentation | 9 | ☐ |
| Code Quality | 4 | ☐ |
| File Structure | 4 | ☐ |
| Version Control | 3 | ☐ |
| **Total** | **44** | ☐ |

---

## Sign-off

- [ ] All checklist items verified
- [ ] Release approved by: ________________
- [ ] Date: ________________

---

*This checklist was generated for the Hodge Conjecture Lean 4 Formalization project.*
