/-!
# Track B: Analytic/GMT Core

This module exports all the analytic machinery for currents, calibrations,
and geometric measure theory needed for the Hodge Conjecture proof.

## Contents

1. **Forms**: Differential forms and exterior derivative
2. **Norms**: Kähler metric, pointwise comass, global comass
3. **Currents**: Currents as linear functionals, mass norm, boundary
4. **IntegralCurrents**: Rectifiable sets, integer multiplicities
5. **Calibration**: Calibrating forms, calibrated currents, spine theorem

## Key Results

- `spine_theorem`: Mass defect ≤ 2 · mass(G) for T = S - G with S calibrated
- `limit_is_calibrated`: Vanishing defect + convergence ⟹ calibrated limit
- `calibration_inequality`: T(ψ) ≤ mass(T) for calibrating ψ

## Usage

```lean
import Hodge.Analytic

-- Access the machinery
#check Current
#check CalibratingForm
#check isCalibrated
#check spine_theorem
#check limit_is_calibrated
```
-/

import Hodge.Analytic.Forms
import Hodge.Analytic.Norms
import Hodge.Analytic.Currents
import Hodge.Analytic.IntegralCurrents
import Hodge.Analytic.Calibration
import Hodge.Analytic.Grassmannian
import Hodge.Analytic.FlatNorm
import Hodge.Analytic.TypeDecomposition

/-! ## Summary of Key Definitions

| Definition | Type | Description |
|------------|------|-------------|
| `SmoothForm n X k` | Type | Smooth k-forms on X |
| `KahlerForm n X` | Structure | Closed positive (1,1)-form |
| `comass` | ℝ | Global comass norm |
| `Current n X k` | Type | Linear functionals on forms |
| `Current.mass` | ℝ | Dual norm to comass |
| `IntegralCurrent n X k` | Structure | Currents with integer multiplicity |
| `CalibratingForm ω_K k` | Structure | Closed form with comass ≤ 1 |
| `isCalibrated` | Prop | mass(T) = T(ψ) |
| `calibrationDefect` | ℝ | mass(T) - T(ψ) |
-/
