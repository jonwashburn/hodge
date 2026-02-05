# Agent Task: AlgebraicSupportImpl — Algebraic Subvarieties as Closed Submanifolds

## Target File
`Hodge/Deep/Pillars/AlgebraicSupportImpl.lean`

## Sorries to Eliminate (3)

### 1. `data_of` (line ~28)
**Type**: `(V : AlgebraicSubvariety n X) → ClosedSubmanifoldData n X (2 * (n - V.codim))`
**Goal**: Given an algebraic subvariety V, construct closed submanifold data for it.

**Strategy**:
- Read the definition of `ClosedSubmanifoldData` (in `Hodge/Analytic/Integration/`)
- Read `AlgebraicSubvariety` (in `Hodge/Classical/GAGA.lean`)
- Construct the data by providing:
  - `carrier`: V.carrier (the underlying set)
  - `dim_eq`: proof that the dimension is 2*(n - V.codim)
  - Other fields from the structure
- Use the fact that smooth algebraic subvarieties of projective manifolds are
  automatically closed submanifolds (Chow + implicit function theorem)

### 2. `carrier_eq` (line ~31)
**Type**: `∀ V, (data_of V).carrier = V.carrier`
**Goal**: The carrier of the constructed data equals the algebraic subvariety's carrier.

**Strategy**: If `data_of` constructs data with `carrier := V.carrier`, this is `rfl`.

### 3. `support_dim` (line ~44)
**Type**: Codimension of the signed cycle support
**Goal**: The support of Z (union of pos and neg parts) has the correct codimension.

**Strategy**:
- Read `SignedAlgebraicCycleSupportCodimData` definition
- The support is `Z.pos ∪ Z.neg`
- Each part is algebraic of codimension p
- Union of two codimension-p sets has codimension p

## Key Files to Read
- `Hodge/Deep/Pillars/AlgebraicSupportImpl.lean` (target)
- `Hodge/Classical/GAGA.lean` (typeclass definitions)
- `Hodge/Analytic/Integration/ClosedSubmanifoldData.lean` (if exists)
- `Hodge/Analytic/Currents.lean` (ClosedSubmanifoldData)

## Verification
```bash
lake build Hodge.Deep.Pillars.AlgebraicSupportImpl
```
