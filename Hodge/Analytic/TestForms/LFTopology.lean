/-
Copyright (c) 2024 Hodge Conjecture Formalization Project. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Analysis.Distribution.TestFunction
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Hodge.Basic

/-!
# LF-Topology on Test Forms

This file develops the LF-space (locally convex inductive limit) topology on
compactly supported smooth differential forms.

## Main Definitions

* `TestFormK` - Smooth k-forms with support in a compact set K
* `TestForm` - The LF-space of compactly supported k-forms (colimit over K)
* `TestForm.topology` - The LF topology

## Main Results

* `TestFormK.isFrechet` - Each D^k_K(X) is a Fréchet space
* `TestForm.isLF` - D^k(X) is an LF-space
* `TestForm.hausdorff` - The LF topology is Hausdorff

## References

* Mathlib `Analysis.Distribution.TestFunction`
* Hörmander, "The Analysis of Linear Partial Differential Operators I"
* [Washburn-Barghi, Sections 4-5]

## Implementation Notes

We build on Mathlib's `𝓓(Ω, F)` infrastructure for Euclidean domains,
then extend to manifolds via charts.
-/

noncomputable section

open scoped Distributions Manifold
open TopologicalSpace Classical

namespace Hodge.TestForms

variable {n : ℕ} {X : Type*}
  [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X]

/-! ## Stage 1.1: Test forms on Euclidean domains -/

/-- The fiber type for k-forms: alternating k-linear maps to ℂ. -/
abbrev FormFiber (n k : ℕ) := (EuclideanSpace ℂ (Fin n)) [⋀^Fin k]→L[ℂ] ℂ

/-- Test k-forms on an open set Ω ⊆ ℂⁿ with the LF topology. 
    This is Mathlib's 𝓓(Ω, F) specialized to form-valued functions. -/
abbrev EuclidTestForm (n k : ℕ) (Ω : Opens (EuclideanSpace ℂ (Fin n))) :=
  𝓓(Ω, FormFiber n k)

/-! ## Stage 1.2: Compact support pieces -/

variable (K : TopologicalSpace.Compacts X) (k : ℕ)

/-- Smooth k-forms on X with support contained in K.
    This is the Fréchet piece of the LF-space. -/
structure TestFormK where
  /-- The underlying form as a section -/
  toFun : X → FormFiber n k
  /-- Smoothness -/
  smooth : Smooth (𝓒_complex n) 𝓘(ℂ, FormFiber n k) toFun
  /-- Support contained in K -/
  support_subset : Function.support toFun ⊆ K

namespace TestFormK

instance : CoeFun (TestFormK (n := n) K k) (fun _ => X → FormFiber n k) :=
  ⟨TestFormK.toFun⟩

/-- The zero form. -/
instance : Zero (TestFormK (n := n) K k) where
  zero := ⟨0, smooth_const, by simp [Function.support]⟩

/-- Addition of test forms. -/
instance : Add (TestFormK (n := n) K k) where
  add f g := ⟨f.toFun + g.toFun, f.smooth.add g.smooth, by
    refine (Function.support_add _ _).trans ?_
    exact Set.union_subset f.support_subset g.support_subset⟩

/-- Scalar multiplication. -/
instance : SMul ℂ (TestFormK (n := n) K k) where
  smul c f := ⟨c • f.toFun, f.smooth.const_smul c, by
    refine (Function.support_smul_subset_right c _).trans ?_
    exact f.support_subset⟩

/-- TestFormK is a Fréchet space (to be proven). -/
theorem isFrechet : sorry := sorry

end TestFormK

/-! ## Stage 1.3: The LF-space colimit -/

/-- The LF-space of compactly supported test k-forms on X.
    Defined as the colimit of TestFormK over compact exhaustion. -/
structure TestForm (n : ℕ) (X : Type*) (k : ℕ)
    [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
    [IsManifold (𝓒_complex n) ⊤ X] where
  /-- The underlying function -/
  toFun : X → FormFiber n k
  /-- Smoothness -/
  smooth : Smooth (𝓒_complex n) 𝓘(ℂ, FormFiber n k) toFun
  /-- Compact support -/
  hasCompactSupport : HasCompactSupport toFun

namespace TestForm

variable {n X k}

instance : CoeFun (TestForm n X k) (fun _ => X → FormFiber n k) :=
  ⟨TestForm.toFun⟩

/-- The LF topology on TestForm. -/
instance instTopologicalSpace : TopologicalSpace (TestForm n X k) := sorry

/-- The LF topology is Hausdorff. -/
theorem hausdorff : T2Space (TestForm n X k) := sorry

/-- The LF topology makes TestForm a topological vector space. -/
instance instTopologicalAddGroup : TopologicalAddGroup (TestForm n X k) := sorry

/-- TestForm is locally convex. -/
instance instLocallyConvexSpace : LocallyConvexSpace ℂ (TestForm n X k) := sorry

/-- TestForm is an LF-space (strict inductive limit of Fréchet spaces). -/
theorem isLFSpace : sorry := sorry

end TestForm

end Hodge.TestForms
