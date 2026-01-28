# Stage 6 (C): Cycle Class + ℚ-Structure + Cohomology Bridges — Strategy

Stage 6 sits at the junction of Track A (GMT/currents) and Track B (analytic/algebraic geometry):

- define a cycle class map \(Z \mapsto [Z] \in H^{2p}(X; \mathbb{Z})\),
- compare with de Rham classes \(H^{2p}_{dR}(X)\),
- express rationality / ℚ-structure,
- connect to Poincaré duality and fundamental classes.

## 1. What Mathlib already has

Mathlib includes **singular homology**:

- `Mathlib.AlgebraicTopology.SingularHomology.Basic`

Mathlib also has:

- substantial homological algebra (`CategoryTheory`, chain complexes, derived functors),
- de Rham/cohomology infrastructure in parts, but not a single “drop-in” `H^*(X; ℤ)` API matching
  classical textbook statements for manifolds.

So Stage 6 is partly “wire existing Mathlib pieces”, partly “build missing bridge lemmas”.

## 2. Recommended staged implementation

### Step A: pick a cohomology model

Two viable Lean directions:

1. **Define singular cohomology** as the homology of the dual cochain complex:
   - start from singular chains `C_*(X; ℤ)`,
   - define cochains `Hom(C_n, A)` and differentials,
   - define `H^n(X; A)` as `H_n` of that cochain complex.

2. **Use sheaf cohomology** machinery where available, then relate to singular/de Rham.

For the Hodge pipeline, option (1) is usually the most direct.

### Step B: de Rham cohomology and de Rham isomorphism

The plan needs:

- `H^k_{dR}(X) ≅ H^k(X; ℝ)` for smooth manifolds `X`.

This is a major theorem; expect substantial development unless Mathlib already has it in a usable form.

### Step C: ℚ-structure / rationality

Goal:

- define `H^k(X; ℚ)` and map it into `H^k(X; ℝ)`,
- state “class is rational” as membership in the image.

### Step D: cycle class map + Poincaré duality

Given a codimension-`p` cycle `Z`, define:

- a homology fundamental class `[Z] ∈ H_{2n-2p}(X; ℤ)` (or cohomology PD class),
- a cohomology class `cl(Z) ∈ H^{2p}(X; ℤ)`.

Then Poincaré duality provides:

- `H_{2n-2p}(X; ℤ) ≅ H^{2p}(X; ℤ)`.

In the currents approach, PD is realized by pairing with forms / integration currents, so Stage 6 depends
heavily on Stage 1–2 foundations.

## 3. Recommended next Lean files (new, off proof track first)

- `Hodge/Cohomology/Stage6/SingularCochains.lean`
  - define cochain complex from singular chains, define cohomology groups
- `Hodge/Cohomology/Stage6/DeRham.lean`
  - define de Rham cohomology in the repo’s setting (or connect to Mathlib if present)
- `Hodge/Cohomology/Stage6/DeRhamIso.lean`
  - statement + proof plan for de Rham isomorphism
- `Hodge/Cohomology/Stage6/PoincareDuality.lean`
  - PD statement + connection to currents integration pairing
- `Hodge/Cohomology/Stage6/CycleClass.lean`
  - cycle class map, functoriality, integer/rational structures

## 4. Practical note

Stage 6 is not “just wiring”: de Rham isomorphism and Poincaré duality are major theorems in Lean unless
Mathlib already provides them in a convenient form. The key risk is underestimating this stage; the
best mitigation is to start Stage 6 early with “skeleton + exact dependency checklist”.

