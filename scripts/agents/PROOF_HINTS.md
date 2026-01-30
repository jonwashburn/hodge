# Agent Proof Hints (Updated 2026-01-30)

These hints are tuned to the **current** Phase‑1 architecture:

- `SmoothForm` is seminormed by comass (NOT discrete topology).
- `Current` is `SmoothForm →L[ℝ] ℝ`.
- Continuity proofs should come from **bounded linear maps**, not `continuous_of_discreteTopology`.

## 1. Core functional-analytic patterns

### 1.1 Build a continuous linear map from a bound

If you can produce a linear map `f : E →ₗ[ℝ] F` and a bound `∃ C, ∀ x, ‖f x‖ ≤ C * ‖x‖`, then:

```lean
exact f.mkContinuousOfExistsBound hbound
```

This is the standard way to package “bounded linear functional” as `→L[ℝ]`.

### 1.2 Get a bound from a `Current` (opNorm)

`Current.toFun` is a `ContinuousLinearMap`, so you automatically get:

```lean
-- |T(ω)| ≤ ‖T‖ * ‖ω‖
simpa [Real.norm_eq_abs] using (T.toFun.le_opNorm ω)
```

### 1.3 Boundary evaluation simplification

Use the simp lemma:

```lean
by simp [Current.boundary_toFun]
```

to rewrite `(Current.boundary T).toFun ω` into `T.toFun (smoothExtDeriv ω)`.

## 2. Algebra on currents/forms (recommended rewrites)

- **Addition / subtraction**:
  - Rewrite `S - T` as `S + -T` with `sub_eq_add_neg`.
  - Use `simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]`.

- **Linearity of evaluation**:
  - Use `T.toFun.map_add` and `T.toFun.map_smul`.

## 3. Practical “don’t get stuck” advice

### 3.1 Avoid old discrete-topology hacks

If you see/think “`continuous_of_discreteTopology`”, that is almost certainly wrong now.
Replace with `mkContinuousOfExistsBound` or `ContinuousLinearMap.le_opNorm`.

### 3.2 When `simp` doesn’t fire on `Current` arithmetic

Sometimes rewriting via the constructor defs is easier:

```lean
simp [Current.add_curr, Current.neg_curr, add_assoc, add_left_comm, add_comm]
```

## 4. What to work on (priority)

Run:

```bash
./scripts/audit_stubs.sh --full
```

and prioritize:

1. `Hodge/Kahler/Main.lean` remaining `sorry` (deep calibration defect = 0)
2. Only after that (or if explicitly requested): eliminate explicit axioms in
   `Hodge/Analytic/Integration/SubmanifoldIntegral.lean` and `Hodge/Classical/GAGA.lean`.

## 5. Hard rules (always enforced)

- No `admit`.
- No trivializations (`:= trivial`, `:= True`, `⟨⟩`, etc).
- Don’t revert Phase‑1 refactors (SmoothForm discrete / Current carrying “bound” field).

