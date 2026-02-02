import Hodge.Analytic.Laplacian.Codifferential

/-!
# Hodge Laplacian Δ

This module introduces a structurally correct definition of the **Hodge Laplacian**
\(\Delta = d\delta + \delta d\) on smooth forms.

The deeper analytic results (ellipticity, finite-dimensionality of harmonic forms,
Hodge decomposition) are developed in subsequent files.
-/

noncomputable section

open Classical

set_option autoImplicit false

universe u

variable {n : ℕ} {X : Type u}
  [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]

/-! Local cast helpers (distribute `castForm` over algebraic operations). -/

private lemma castForm_add {k k' : ℕ} (h : k = k') (ω η : SmoothForm n X k) :
    castForm (n := n) (X := X) h (ω + η) =
      castForm (n := n) (X := X) h ω + castForm (n := n) (X := X) h η := by
  subst h; rfl

private lemma castForm_smul {k k' : ℕ} (h : k = k') (c : ℂ) (ω : SmoothForm n X k) :
    castForm (n := n) (X := X) h (c • ω) =
      c • castForm (n := n) (X := X) h ω := by
  subst h; rfl

/-- **Hodge Laplacian** Δ on `k`-forms.

`Δω = d(δω) + δ(dω)`.

Note (repo-specific model): in this codebase, `⋆` is a fiberwise operator on complex-linear
forms, so it has degree `k ↦ (n - k)`. Accordingly, `δ = ⋆ d ⋆` has degree
`k ↦ (k - 1)` only when `k ≤ n`. The `δ d` term is therefore included only for `k < n`. -/
noncomputable def laplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  castForm (by omega) (smoothExtDeriv (codifferential (n := n) (X := X) (k := k) ω)) +
    (if hkn : k = n then
      0
    else
      castForm (by
        -- In the non-top-degree case, `k < n`, so `δ : Ω^{k+1} → Ω^k` has the expected degree.
        have hklt : k < n := lt_of_le_of_ne hk' hkn
        have hk1 : 1 ≤ n - k := (Nat.succ_le_iff).2 (Nat.sub_pos_of_lt hklt)
        have hnk : n - (k + 1) + 1 = n - k := by
          calc
            n - (k + 1) + 1 = (n - Nat.succ k) + 1 := by
              rw [Nat.add_one k]
            _ = (n - k - 1) + 1 := by
              exact congrArg (fun t => t + 1) (Nat.sub_succ n k)
            _ = n - k := by simpa using (Nat.sub_add_cancel hk1)
        calc
          n - (n - (k + 1) + 1) = n - (n - k) := by simpa [hnk]
          _ = k := Nat.sub_sub_self hk')
        (codifferential (n := n) (X := X) (k := k + 1) (smoothExtDeriv ω)))

/-- Alias: the Hodge Laplacian Δ = dδ + δd. -/
noncomputable abbrev hodgeLaplacian_construct {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (ω : SmoothForm n X k) : SmoothForm n X k :=
  laplacian_construct (n := n) (X := X) (k := k) hk hk' ω

/-! ### Linearity of `laplacian_construct` -/

theorem laplacian_construct_zero {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' 0 = 0 := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct]
  · simp [laplacian_construct, hkn]

theorem laplacian_construct_add {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (α β : SmoothForm n X k) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' (α + β) =
    laplacian_construct (n := n) (X := X) (k := k) hk hk' α +
      laplacian_construct (n := n) (X := X) (k := k) hk hk' β := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct, smoothExtDeriv_add, castForm_add, add_assoc, add_left_comm, add_comm]
  ·
    simp [laplacian_construct, hkn, smoothExtDeriv_add, castForm_add,
      add_assoc, add_left_comm, add_comm]

theorem laplacian_construct_smul {k : ℕ} (hk : 1 ≤ k) (hk' : k ≤ n)
    (c : ℂ) (α : SmoothForm n X k) :
    laplacian_construct (n := n) (X := X) (k := k) hk hk' (c • α) =
      c • laplacian_construct (n := n) (X := X) (k := k) hk hk' α := by
  classical
  by_cases hkn : k = n
  · subst hkn
    simp [laplacian_construct, smoothExtDeriv_smul, castForm_smul, smul_add]
  ·
    simp [laplacian_construct, hkn, smoothExtDeriv_smul, castForm_smul, smul_add]

/-- Laplacian as a ℂ-linear map (using the current definition of Δ). -/
noncomputable def laplacianLinearMap (k : ℕ) (hk : 1 ≤ k) (hk' : k ≤ n) :
    SmoothForm n X k →ₗ[ℂ] SmoothForm n X k where
  toFun ω := laplacian_construct (n := n) (X := X) (k := k) hk hk' ω
  map_add' := laplacian_construct_add (n := n) (X := X) (k := k) hk hk'
  map_smul' := by
    intro c ω
    simp only [RingHom.id_apply]
    exact laplacian_construct_smul (n := n) (X := X) (k := k) hk hk' c ω
