# Agent Proof Hints

These hints document proof patterns that work for the Hodge formalization.
Use these strategies when attempting to eliminate `sorry` statements.

## Successful Proof Patterns

### 1. Triangle Inequality for iSup (mass_add)

When proving `⨆ ω, ‖f(ω)‖ + ⨆ ω, ‖g(ω)‖ ≥ ⨆ ω, ‖f(ω) + g(ω)‖`:

```lean
apply iSup₂_le
intro ω hω
have h1 : (‖(S + T) ω‖₊ : ℝ≥0∞) ≤ ‖S ω‖₊ + ‖T ω‖₊ := by
  have : (S + T) ω = S ω + T ω := LinearMap.add_apply S T ω
  rw [this]
  exact_mod_cast nnnorm_add_le (S ω) (T ω)
have h2 : (‖S ω‖₊ : ℝ≥0∞) ≤ ⨆ ω' ∈ comassUnitBall n X k, (‖S ω'‖₊ : ℝ≥0∞) := by
  apply le_iSup₂_of_le ω hω
  rfl
-- ... combine with add_le_add
```

### 2. Infimum Upper Bound (flatNorm_le_mass)

When proving `⨅ x, f(x) ≤ specific_value`:

```lean
have h : T = T + Current.boundary 0 := by simp [Current.boundary]
calc ⨅ R, ⨅ S, ⨅ _ : T = R + Current.boundary S, mass R + mass S
    ≤ mass T + mass (0 : Current n X (k + 1)) := by
      apply iInf_le_of_le T
      apply iInf_le_of_le 0
      apply iInf_le_of_le h
      rfl
  _ = mass T + 0 := by rw [mass_zero]
  _ = mass T := add_zero _
```

### 3. Placeholder Definitions (comass = 0)

When `comass` is defined as 0:
- `comass_add` and `comass_smul` become trivial via `simp [comass]`
- `mass` becomes trivial via the same simplification

### 4. Zero Current Arguments

When `submanifoldIntegral` is defined as 0:
- `integrationCurrent Z = 0` can be shown with:
```lean
apply LinearMap.ext
intro ω
simp only [integrationCurrent, submanifoldIntegral, LinearMap.coe_mk, 
           AddHom.coe_mk, LinearMap.zero_apply]
```

---

## Remaining Sorries with Hints

### GMT/Mass.lean:111 - mass_smul
```lean
mass (c • T) = ‖c‖₊ * mass T
```
**Hint**: Need `ENNReal.mul_iSup₂` or manual manipulation. Key step:
```lean
have h : ∀ ω, (c • T) ω = c • T ω := fun ω => LinearMap.smul_apply c T ω
simp_rw [h, nnnorm_smul]
-- Then factor out ‖c‖₊ from the iSup using ENNReal multiplication properties
```

### GMT/FlatNorm.lean:50 - flatNorm_eq_zero_iff
```lean
flatNorm T = 0 ↔ ∃ S, T = Current.boundary S
```
**Hint**: The ← direction requires showing the infimum is 0 by taking R = 0, S = the witness.
The → direction requires showing mass R = mass S = 0 implies R = 0 and T = ∂S.

### GMT/FlatNorm.lean:69 - flatNorm_add
```lean
flatNorm (S + T) ≤ flatNorm S + flatNorm T
```
**Hint**: Use the definition. If S = R₁ + ∂S₁ and T = R₂ + ∂S₂, then:
S + T = (R₁ + R₂) + ∂(S₁ + S₂). Use `mass_add` for both parts.

### GMT/FlatNorm.lean:74 - flatNormTopology
```lean
def flatNormTopology : TopologicalSpace (Current n X k)
```
**Hint**: Use `UniformSpace.toTopologicalSpace` with the flat norm as metric,
or define via `TopologicalSpace.induced` from the flat norm function.

### GMT/FlatNorm.lean:90 - isIntegral
```lean
isIntegral : Prop := sorry
```
**Hint**: This is a placeholder for "integer multiplicities". Could define as True 
temporarily, or reference the slicing measure being integer-valued.

### GMT/FlatNorm.lean:108 - federerFleming_compactness
**Hint**: This is a deep theorem. For scaffolding, either:
- Define it as an axiom with honest documentation
- Use `sorry` with a note about what it requires

### GMT/Calibration.lean:88 - current_form_bound  
```lean
‖T ω‖ ≤ (mass T).toReal * comass ω
```
**Hint**: With comass = 0, RHS = 0. This can't be proven without proper comass.
Leave as sorry until comass is properly defined.

### GMT/Calibration.lean:97 - calibrated_minimizes_mass
**Hint**: This is Harvey-Lawson calibration theorem. Deep result requiring
the calibration inequality and proper GMT infrastructure.

### GMT/Calibration.lean:111 & 121 - IsSupportedOnAnalyticVariety
**Hint**: These require analytic variety theory from AlgGeom. Keep as sorry
until that infrastructure exists.

### Kahler/Main.lean:262 - calibration defect → 0
**Hint**: This is CORE HODGE. The proof requires:
1. Show microstructure sequence has vanishing defect
2. Use GMT compactness to extract limit
3. Apply Harvey-Lawson to get analytic support

### Classical/GAGA.lean:590 - fundamental_eq_representing
**Hint**: This is CORE HODGE. The proof requires:
1. Integration current of support has Poincaré dual = representing form
2. Uses the full spine bridge construction
3. Reference paper Sections 8-10

---

## Key Lemmas to Know

- `LinearMap.add_apply`: `(S + T) ω = S ω + T ω`
- `LinearMap.smul_apply`: `(c • T) ω = c • T ω`
- `nnnorm_add_le`: triangle inequality for nnnorm
- `nnnorm_smul`: `‖c • x‖₊ = ‖c‖₊ * ‖x‖₊`
- `le_iSup₂_of_le`: prove ≤ iSup by exhibiting witness
- `iSup₂_le`: prove iSup ≤ something by proving for all elements
- `iInf_le_of_le`: prove iInf ≤ something by exhibiting witness
- `ENNReal.mul_iSup`: factor out multiplication from iSup
- `mass_zero`: `mass 0 = 0`
