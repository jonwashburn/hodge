# Agent Task: SpineBridgeImpl — Fundamental Class = Representing Form

## Target File
`Hodge/Deep/Pillars/SpineBridgeImpl.lean`

## Sorries to Eliminate (1)

### `fundamental_eq_representing` (line ~41)
**Type**: `SpineBridgeData_data.fundamental_eq_representing`
**Goal**: The geometric fundamental class of a spine-produced cycle equals the
representing form's cohomology class.

**Mathematical Content**:
For a signed algebraic cycle Z produced by the SYR → Harvey-Lawson → GAGA pipeline:
  [FundamentalClass(Z)] = [γ] in H^{2p}(X, ℝ)

where:
- FundamentalClass(Z) = regularize(integrationCurrent(Z)) = PoincaréDual form
- γ is the representing form that Z was constructed from

The key steps are:
1. Z was constructed from γ via Harvey-Lawson: T = [Z]
2. The integration current [Z] is regularized to a smooth form η_Z
3. [η_Z] = [[Z]] in cohomology (regularization preserves class)
4. [[Z]] = [γ] because Z was constructed to represent [γ]

**Strategy**:
1. Read `SpineBridgeData_data` definition to understand exact type signature
2. Read how `cycleClass_geom_data` is computed from `FundamentalClassSet_data`
3. Check if the bridge can be proved by:
   - Unfolding definitions
   - Using the fact that the cycle carries `representingForm := γ`
   - Connecting through the regularization pipeline

**This is likely the hardest sorry** because it connects the geometric (measure-theoretic)
and cohomological (algebraic) sides of the proof. It may require proving that:
- Integration currents are closed (Stokes on cycles)
- Regularization preserves cohomology class
- The Harvey-Lawson construction preserves the target class

Check if the existing infrastructure provides enough to close this gap.

## Key Files to Read
- `Hodge/Deep/Pillars/SpineBridgeImpl.lean` (target)
- `Hodge/Deep/Pillars/PoincareDuality.lean` (infrastructure)
- `Hodge/Classical/GAGA.lean` (SpineBridgeData_data definition)
- `Hodge/Classical/CycleClass.lean` (cycle class infrastructure)
- `Hodge/Classical/PoincareDualityFromCurrents.lean` (PD interface)

## Verification
```bash
lake build Hodge.Deep.Pillars.SpineBridgeImpl
```
