# Test Coverage Documentation

**Last Updated**: 2026-01-21 (Round 12, Agent 3: R12-A3-TESTS)

## Overview

This document describes the test coverage for the Hodge Conjecture Lean 4 formalization project.

## Test Files

| File | Description | Tests |
|------|-------------|-------|
| `Hodge/Tests/MasterTests.lean` | Master test harness | 27+ tests |
| `Hodge/Analytic/Advanced/IntegrationTests.lean` | Exterior derivative tests | 10 tests |
| `Hodge/Analytic/Laplacian/ConnectionTests.lean` | Laplacian/connection tests | Per-module |
| `Hodge/Kahler/Lefschetz/LefschetzTests.lean` | Lefschetz operator tests | Per-module |
| `Hodge/GMT/GMTTests.lean` | Geometric measure theory tests | Per-module |

## Test Categories

### 1. Cross-Module Smoke Tests

Verify basic cross-module type compatibility:
- Cycle class forms are closed
- De Rham cohomology classes can be constructed
- Integration currents are accessible

### 2. Top-Form Integration (Round 10)

**Tests 1-4**: `topFormIntegral_real'` nontriviality

| Test | Property | Status |
|------|----------|--------|
| Test 1 | `topFormIntegral_real'` uses `integrateDegree2p` | ✅ |
| Test 2 | Linearity: `topFormIntegral_real' (c • η₁ + η₂) = ...` | ✅ |
| Test 3 | Zero form: `topFormIntegral_real' 0 = 0` | ✅ |
| Test 4 | Complex version uses real: `topFormIntegral_complex η = Complex.ofReal ...` | ✅ |

### 3. L² Inner Product (Round 10)

**Tests 5-8**: `L2InnerProduct` algebraic properties

| Test | Property | Status |
|------|----------|--------|
| Test 5 | Structure: uses `L2InnerProductData.trivial` | ✅ |
| Test 6 | Left-linearity (sesquilinear) | ✅ |
| Test 7 | Hermitian symmetry | ✅ |
| Test 8 | Positive semi-definiteness | ✅ |

### 4. Integration Infrastructure Edge Cases (Round 12)

**Tests 9-13**: `integrateDegree2p` degree dispatch

| Test | Property | Status |
|------|----------|--------|
| Test 9 | Odd degree (k=3) returns 0 | ✅ |
| Test 10 | Even degree (k=4) is defined | ✅ |
| Test 11 | Linearity | ✅ |
| Test 12 | Empty set returns 0 | ✅ |
| Test 13 | Bounded by form norm | ✅ |

**Tests 14-18**: `submanifoldIntegral` properties

| Test | Property | Status |
|------|----------|--------|
| Test 14 | Additivity: `∫(ω₁ + ω₂) = ∫ω₁ + ∫ω₂` | ✅ |
| Test 15 | Zero form: `∫0 = 0` | ✅ |
| Test 16 | Scalar mult: `∫(c • ω) = c * ∫ω` | ✅ |
| Test 17 | Bounded by form norm | ✅ |
| Test 18 | `LinearMap` interface | ✅ |

### 5. Calibration Theory (Round 12)

**Tests 19-24**: `CalibratingForm` and calibration inequality

| Test | Property | Status |
|------|----------|--------|
| Test 19 | `KählerCalibration` is a `CalibratingForm` | ✅ |
| Test 20 | Form is closed | ✅ |
| Test 21 | Comass ≤ 1 | ✅ |
| Test 22 | Calibration inequality: `T(ψ) ≤ mass(T)` | ✅ |
| Test 23 | Calibration defect ≥ 0 | ✅ |
| Test 24 | `isCalibrated ↔ defect = 0` | ✅ |

### 6. Negative Tests (Round 12)

**Tests 25-27**: Invalid input handling

| Test | Property | Status |
|------|----------|--------|
| Test 25a | k=1 (odd) → `integrateDegree2p` returns 0 | ✅ |
| Test 25b | k=5 (odd) → `integrateDegree2p` returns 0 | ✅ |
| Test 26 | Empty set → `submanifoldIntegral` returns 0 | ✅ |
| Test 27 | Zero form on empty set → returns 0 | ✅ |

## Exterior Derivative Tests (IntegrationTests.lean)

| Test | Property | Status |
|------|----------|--------|
| Test 1a | `d(0) = 0` | ✅ |
| Test 1b | Zero form is closed | ✅ |
| Test 2a | `d² = 0` | ✅ |
| Test 2b | `dω` is always closed | ✅ |
| Test 2c | Exact implies closed | ✅ |
| Test 3a | Leibniz rule | ✅ |
| Test 3b | Wedge of closed forms is closed | ✅ |
| Test 4a-d | Linearity properties | ✅ |
| Test 5a-b | Connection to `ContMDiffForm.extDerivForm` | ✅ |

## Running Tests

```bash
# Build all tests
lake build Hodge.Tests.MasterTests

# Full verification suite
./scripts/audit_stubs.sh --full
./scripts/audit_faithfulness.sh
lake env lean Hodge/Utils/DependencyCheck.lean
```

## Coverage Gaps

### Known Untested Areas

1. **KählerCalibration nontrivial form** (Agent 1 pending)
   - Currently uses `form := 0` stub
   - Tests will need updating when Agent 1 implements `kahlerPow p`

2. **L² Inner Product nontrivial implementation** (Agent 2 pending)
   - Currently uses `L2InnerProductData.trivial`
   - Tests will need updating when nontrivial inner product is implemented

3. **Hodge Star operator**
   - Currently stubbed as `HodgeStarData.trivial`
   - Not tested directly

### Future Test Additions

When Agent 1 completes `R11-A1-CALIBRATION`:
- Add test for `KählerCalibration.form = kahlerPow p`
- Add test for Wirtinger inequality (comass bound)

When Agent 2 completes L² implementation:
- Add test for `L2InnerProduct ω ω > 0` for non-zero ω
- Add test for actual wedge+star+integration formula

## Test Statistics

| Category | Tests | Passing |
|----------|-------|---------|
| Cross-module | 3 | ✅ |
| Top-form integration | 4 | ✅ |
| L² inner product | 4 | ✅ |
| integrateDegree2p | 5 | ✅ |
| submanifoldIntegral | 5 | ✅ |
| Calibration | 6 | ✅ |
| Negative tests | 4 | ✅ |
| **Total** | **31+** | **✅** |

## Verification Commands

```bash
# Quick syntax check
lake build Hodge.Tests.MasterTests

# Full axiom check
lake env lean Hodge/Utils/DependencyCheck.lean
# Expected: 'hodge_conjecture_data' depends on axioms: [propext, Classical.choice, Quot.sound]

# Stub audit
./scripts/audit_stubs.sh --full
```
