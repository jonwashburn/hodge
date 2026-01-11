# Remaining `sorry` Report

## Summary (2026-01-10)

- **Global (in `Hodge/`)**: 16 occurrences of `sorry` in code (plus 1 documentation-only mention in `Hodge/Analytic/Advanced.lean`).
- **Dependency-closure**: `#print axioms hodge_conjecture'` contains `sorryAx`, so **at least one `sorry` is on the critical path** for the main theorem as currently implemented.

## Dependency closure (from `Hodge/Utils/AuditAxioms.lean`)

- `hodge_conjecture'` depends on `sorryAx`
- `hodge_conjecture''` depends on `sorryAx`

(`sorryAx` appears once even if multiple `sorry`s are used in the dependency closure.)

## Locations (within `Hodge/`)

### `Hodge/Kahler/Main.lean`
- **L204**: `omega_pow_algebraic` — missing proof that a positive rational multiple of \([\omega^p]\) is algebraic.

### `Hodge/Kahler/Manifolds.lean`
- **L267**: `hodgeStar_hodgeStar` — involution/sign law for the Hodge star.
- **L363**: `adjointDeriv_squared` — codifferential squares to 0 (\(\delta^2 = 0\)).
- **L494**: `isHarmonic_implies_coclosed` — harmonic implies coclosed.
- **L505**: `isHarmonic_implies_closed` — harmonic implies closed.

### `Hodge/Cohomology/HodgeDecomposition.lean`
- **L159**: `isPPClass_iff_isPQClass` — missing bridge `isPPForm' → isPQForm`.
- **L163**: `isPPClass_iff_isPQClass` — missing bridge `isPQForm → isPPForm'`.
- **L188**: `isDolbeaultExact_imp_closed` — degree cast arithmetic / transport.
- **L245**: `lefschetz_preserves_type` — Lefschetz preserves (p,q)-type.
- **L256**: `lefschetz_lambda_lowers_type` — Λ lowers (p,q)-type.

### `Hodge/Cohomology/Basic.lean`
- **L213**: `cohomologous_wedge` — wedge descends to cohomology (Leibniz / exactness proof).
- **L464**: `mul_assoc` — cup product associativity (with degree casts).
- **L485**: `one_mul` — left unit law (with degree casts).
- **L495**: `mul_one` — right unit law (with degree casts).

### `Hodge/Analytic/Currents.lean`
- **L339**: `Current.boundary.bound` — continuity/bound estimate for the current boundary operator.

### `Hodge/Classical/PrimitiveDecomposition.lean`
- **L151**: `PrimitiveDecomposition.decomposition_eq` — a `sorry` is used as a placeholder inside the structure field.

