/-!
# Track C: Algebraic/Kähler Core

This module exports all the Kähler geometry and algebraic machinery
needed for the Hodge Conjecture proof.

## Contents

1. **Manifolds**: Projective and Kähler manifold structures
2. **Cone**: Strongly positive cone K_p and ω^p interiority
3. **SignedDecomp**: Signed decomposition theorem
4. **Microstructure**: Sheet construction and gluing
5. **MainTheorem**: Final assembly of the proof

## Key Results

- `stronglyPositiveCone`: K_p = convexHull(simple calibrated forms)
- `omegaPow_in_interior`: ω^p ∈ int(K_p)
- `signed_decomposition`: γ = γ⁺ - γ⁻ with γ⁻ algebraic, γ⁺ cone-positive
- `cone_positive_is_algebraic`: Cone-positive classes are algebraic
- `hodge_conjecture`: The main theorem

## Usage

```lean
import Hodge.Kahler

-- Access the main theorem
#check hodge_conjecture
#check hodge_conjecture_statement
```
-/

import Hodge.Kahler.Manifolds
import Hodge.Kahler.Cone
import Hodge.Kahler.SignedDecomp
import Hodge.Kahler.Microstructure
import Hodge.Kahler.Main

/-! ## Summary of Key Definitions

| Definition | Type | Description |
|------------|------|-------------|
| `ProjectiveComplexManifold` | Class | Manifold with projective embedding |
| `KahlerManifold` | Class | Manifold with Kähler structure |
| `stronglyPositiveCone` | Set | Convex hull of calibrated forms |
| `isConePositive` | Prop | Form is pointwise in cone |
| `signed_decomposition` | Theorem | γ = γ⁺ - γ⁻ decomposition |
| `hodge_conjecture` | Theorem | Main result |
-/
