# Proof‑track status (ground truth)

This note exists because “how many axioms/sorries remain?” is easy to misstate unless we fix the metric.
The only metric that matters for the final proof is **Lean’s kernel dependency report**:

- `#print axioms hodge_conjecture'`

That command reports exactly the *global* axioms that the theorem’s definition depends on.
It does **not** list:

- assumptions in the statement (e.g. typeclass parameters like `[KahlerManifold n X]`),
- axioms/sorries that exist elsewhere in the repo but are not used by `hodge_conjecture'`.

So, whenever there is disagreement about “where we are”, we treat this output as the ground truth.

---

## How to reproduce the current status

From repo root:

```bash
lake build Hodge.Kahler.Main

cat > /tmp/axioms.lean << 'EOF'
import Hodge.Kahler.Main
#print axioms hodge_conjecture'
EOF

lake env lean /tmp/axioms.lean
```

---

## Current kernel report (as of this commit)

Lean prints:

```
'hodge_conjecture'' depends on axioms: [FundamentalClassSet_represents_class,
 propext,
 Classical.choice,
 Current.smoothExtDeriv_comass_bound,
 LeibnizRule.alternatizeUncurryFin_wedge_left,
 LeibnizRule.alternatizeUncurryFin_wedge_right,
 Quot.sound]
```

Interpretation:

- **Lean standard axioms** (expected):
  - `propext`
  - `Classical.choice`
  - `Quot.sound`
- **Custom proof‑track axioms still remaining** (these are the real “holes”):
  1. `FundamentalClassSet_represents_class`
  2. `Current.smoothExtDeriv_comass_bound`
  3. `LeibnizRule.alternatizeUncurryFin_wedge_left`
  4. `LeibnizRule.alternatizeUncurryFin_wedge_right`

There are **no `sorry`s on the proof track** at this point; the only remaining holes are these named axioms.

---

## What changed in this commit (and why it matters)

### 1) `Hodge/Analytic/DomCoprod.lean`: removed two *unit* axioms for wedge with 0‑forms

We replaced these *axioms* with *theorems*:

- `ContinuousAlternatingMap.wedge_constOfIsEmpty_left`
- `ContinuousAlternatingMap.wedge_constOfIsEmpty_right`

**Why this was possible (core idea)**:

In Mathlib, `AlternatingMap.domCoprod` is defined as a finite sum over the **shuffle quotient**
`Equiv.Perm.ModSumCongr ιa ιb`.  When one index type is empty (`ιa = Fin 0` or `ιb = Fin 0`),
this quotient has exactly one element. Therefore the sum collapses to a single summand, and the
wedge computation reduces to scalar multiplication.

**What we had to prove to make the sum collapse**:

- `Subsingleton (Equiv.Perm.ModSumCongr (Fin 0) (Fin l))`
- `Subsingleton (Equiv.Perm.ModSumCongr (Fin k) (Fin 0))`

These follow by showing `Equiv.Perm.sumCongrHom` is surjective in those empty‑index cases, so the
quotient by its range is trivial.

**Why this matters**:

These unit laws are used downstream (e.g. `smoothWedge_unitForm_left/right`) to make the cup product
have a unit. They were previously “parent axioms”: even if they were not showing up in the
`#print axioms` output for `hodge_conjecture'` at some moments (because that particular proof path
didn’t exercise the unit lemmas), they were still unproved global axioms living in imported code.

This commit removes them as global axioms entirely.

### 2) `Hodge/Analytic/Advanced/LeibnizRule.lean`: added sign‑conversion helper lemmas

We added helper lemmas that make it easier to bridge between:

- the **ℤ‑signs** coming from `AlternatingMap.alternatizeUncurryFin` (Mathlib’s definition uses `(-1 : ℤ)^i`),
- the **ℂ‑signs** that appear naturally in our wedge/complex‑valued form setup.

Concretely, this commit adds lemmas that rewrite the `toAlternatingMap` evaluation of
`ContinuousAlternatingMap.alternatizeUncurryFin` as an explicit sum with **ℂ‑powers** `(-1 : ℂ)^i`.

**Why this matters**:

The last two “small” proof‑track axioms are precisely the two combinatorial identities in
`LeibnizRule.lean`:

- `alternatizeUncurryFin_wedge_right`
- `alternatizeUncurryFin_wedge_left`

Those axioms are about reindexing/shuffle sums and tracking signs. The new lemmas remove one source
of pain (ℤ vs ℂ sign coercions) so the remaining work is purely the shuffle‑bijection bookkeeping.

---

## What is left after we eliminate the two LeibnizRule axioms?

If we prove `LeibnizRule.alternatizeUncurryFin_wedge_left/right` as theorems, then
`#print axioms hodge_conjecture'` should drop from **4 custom axioms** to **2 custom axioms**:

1. `Current.smoothExtDeriv_comass_bound` (analytic functional‑analysis gap)
2. `FundamentalClassSet_represents_class` (GMT + de Rham currents + GAGA bridge)

That “final two” state is the correct next milestone.

---

## Why earlier “axiom counts” can look inconsistent

Two common pitfalls:

1) **Counting `axiom` lines in the repo is not the proof‑track metric.**
It overcounts because it includes axioms that are not used by `hodge_conjecture'`.

2) **Even axioms in imported modules may not appear in `#print axioms`**
if nothing in the dependency cone of `hodge_conjecture'` uses them.
This is why the proof‑track check must always be the kernel report, not greps.

---

## Next actions (most practical path)

1) **Prove the two remaining LeibnizRule axioms** (combinatorics / shuffle‑sum reindexing).
   - This is the highest‑leverage “small” elimination: it removes 2 of the 4 remaining proof‑track holes.

2) Reassess the final two:
   - **`Current.smoothExtDeriv_comass_bound`**: either refactor currents/flat norm to use the
     Federer–Fleming “flat test form” restriction (so we don’t need a false global C⁰ bound),
     or invest in Sobolev/Fréchet infrastructure.
   - **`FundamentalClassSet_represents_class`**: requires serious integration/currents + GAGA;
     either keep as a pillar or build the missing theory.

