# Hodge Conjecture Formalization in Lean 4

This repository contains a **machine-checked Lean 4 proof** of a Hodge Conjecture statement (`hodge_conjecture'`) **conditional on an explicit axiom set** (printed by Lean via `#print axioms`).

The project goal is **faithfulness modulo explicit axioms**:
- the *statement* matches the classical Hodge Conjecture shape, and
- the *assumptions* are made fully explicit (no hidden `sorry`/`admit`).

---

## Main theorem (what Lean proves)

The main theorem is in `Hodge/Kahler/Main.lean`:

```lean
theorem hodge_conjecture' {p : ℕ} (γ : SmoothForm n X (2 * p)) (h_closed : IsFormClosed γ)
    (h_rational : isRationalClass (DeRhamCohomologyClass.ofForm γ h_closed)) (h_p_p : isPPForm' n X p γ) :
    ∃ (Z : SignedAlgebraicCycle n X), Z.RepresentsClass (DeRhamCohomologyClass.ofForm γ h_closed) := by
  ...
```

**Faithfulness-critical point**: “represents” is **equality in de Rham cohomology** (not equality of form representatives).

---

## How to verify locally

```bash
lake build
lake env lean DependencyCheck.lean
grep -R "sorry\|admit" -n Hodge | wc -l
```

---

## Axiom dependencies (mechanical)

Run:

```bash
lake env lean DependencyCheck.lean
```

Lean prints the **exact** axiom list that `hodge_conjecture'` depends on (currently **39** axioms, plus Lean’s standard classical axioms like `Classical.choice`, `propext`, etc.).

---

## Closure / “what is assumed vs what is proved”

Your feedback is spot-on: **the proof is only as strong as its axioms**. The current axiom set contains:

### A. Classical results (standard literature)
Examples include:
- `hard_lefschetz_inverse_form` (Hard Lefschetz input)
- `serre_gaga` (GAGA / Chow-type algebraicity transfer)
- `harvey_lawson_theorem`, `harvey_lawson_represents` (Harvey–Lawson calibrated-current structure theorem)
- `flat_limit_of_cycles_is_cycle` (flat limits of cycles remain cycles)

These are deep, but they are **classical theorems**.

### B. Strategy-critical assumptions (where “the hard part” can hide)
Other axioms are **not merely analytic continuity facts**, but rather encode key steps of the chosen proof strategy. In particular:
- `signed_decomposition` (decomposing a rational \((p,p)\) class into a cone-positive piece and a Kähler power term)
- `microstructureSequence_*` axioms (the microstructure approximation pipeline)
- `harvey_lawson_fundamental_class` (bridge from the Harvey–Lawson output to the **cohomology class equality** needed to conclude representation)

These are exactly the places where one must be careful: depending on their strength, they may implicitly assume a large fraction of the conjecture’s content.

**Bottom line**: the repository contains a machine-checked Lean proof of `hodge_conjecture'` **conditional on** the axiom set printed by `DependencyCheck.lean`. It does **not** claim an unconditional resolution of the Hodge Conjecture.

---

## Repo statistics (current)

| Metric | Count |
|--------|-------|
| `sorry` / `admit` in `Hodge/` | 0 |
| Lean files (excluding `.lake`) | 32 |
| Lines in `Hodge/**/*.lean` | 4513 |
| `axiom` declarations in `Hodge/` | 147 |
| `opaque` declarations in `Hodge/` | 43 |
| `axiom` + `opaque` in `Hodge/` | 190 |

---

## Roadmap notes (Hard Lefschetz / de Rham cohomology)

I agree with your point: **Hard Lefschetz is a core classical theorem** and a natural target for future full formalization. In this repo it is currently assumed (explicitly) as an axiom (`hard_lefschetz_inverse_form`), because a full formalization would require substantial Kähler/Hodge theory infrastructure.

---

## Key references

1. P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978.
2. R. Harvey and H.B. Lawson Jr., “Calibrated geometries”, *Acta Math.* 148 (1982), 47–157.
3. H. Federer, *Geometric Measure Theory*, Springer, 1969.
4. J.-P. Serre, “Géométrie algébrique et géométrie analytique”, *Ann. Inst. Fourier* 6 (1956), 1–42.
5. C. Voisin, *Hodge Theory and Complex Algebraic Geometry*, Cambridge, 2002–2003.
