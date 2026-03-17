import Hodge.WorkInProgress.GMT.LocalCurrents

noncomputable section

open Classical

namespace Hodge.GMT

universe u v

variable {n : ℕ} {k : ℕ}
variable {X : Type u} [MetricSpace X] [ChartedSpace (EuclideanSpace ℂ (Fin n)) X]
  [IsManifold (𝓒_complex n) ⊤ X] [HasLocallyConstantCharts n X]
  [ProjectiveComplexManifold n X] [KahlerManifold n X]
  [Nonempty X] [MeasurableSpace X] [BorelSpace X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace (EuclideanSpace ℂ (Fin n)) Y]
  [IsManifold (𝓒_complex n) ⊤ Y] [HasLocallyConstantCharts n Y]

/-- Pullback of local test forms to the compact source manifold, packaged as a linear map. -/
noncomputable def testFormPullbackLinear (f : X → Y)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f) :
    TestForm n Y k →ₗ[ℝ] SmoothForm n X k where
  toFun := TestForm.pullbackToSmooth (n := n) (k := k) f hf
  map_add' := by
    intro ω₁ ω₂
    simpa using
      (TestForm.pullbackToSmooth_add (n := n) (k := k) (f := f) hf ω₁ ω₂)
  map_smul' := by
    intro r ω
    simpa using
      (TestForm.pullbackToSmooth_smul (n := n) (k := k) (f := f) hf r ω)

/-- Pushforward of a global current to a local current on compactly supported test forms. -/
noncomputable def currentPushforward (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (T : Current n X k) : LocalCurrent n Y k :=
  { toLinear :=
      { toFun := fun ω => T.toFun (TestForm.pullbackToSmooth (n := n) (k := k) f hf ω)
        map_add' := by
          intro ω₁ ω₂
          simp [TestForm.pullbackToSmooth_add]
        map_smul' := by
          intro r ω
          simp [TestForm.pullbackToSmooth_smul] }
    comass_bound := by
      have hC_nonneg : 0 ≤ C := by
        let x : X := Classical.choice (inferInstance : Nonempty X)
        exact (pow_nonneg (norm_nonneg _) _).trans (hC x)
      refine ⟨‖T.toFun‖ * C, ?_⟩
      intro ω
      have hT :
          |T.toFun (TestForm.pullbackToSmooth (n := n) (k := k) f hf ω)| ≤
            ‖T.toFun‖ * ‖TestForm.pullbackToSmooth (n := n) (k := k) f hf ω‖ := by
        simpa [Real.norm_eq_abs] using
          (T.toFun.le_opNorm (TestForm.pullbackToSmooth (n := n) (k := k) f hf ω))
      have hnorm :
          ‖TestForm.pullbackToSmooth (n := n) (k := k) f hf ω‖ ≤
            TestForm.comass ω * C := by
        exact
          TestForm.pullbackToSmooth_norm_le (n := n) (k := k)
            (f := f) hf (C := C) hC ω
      calc
        |T.toFun (TestForm.pullbackToSmooth (n := n) (k := k) f hf ω)| ≤
            ‖T.toFun‖ * ‖TestForm.pullbackToSmooth (n := n) (k := k) f hf ω‖ := hT
        _ ≤ ‖T.toFun‖ * (TestForm.comass ω * C) :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
        _ = (‖T.toFun‖ * C) * TestForm.comass ω := by ring
    boundary_bound := by
      cases k with
      | zero =>
          exact True.intro
      | succ k' =>
          obtain ⟨M, hM⟩ :=
            (T.boundary_bound :
              ∃ M : ℝ, ∀ ω : SmoothForm n X k', |T.toFun (smoothExtDeriv ω)| ≤ M * ‖ω‖)
          set C' : ℝ := max 1 C
          have hC' : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ C' := by
            intro x
            by_cases hle : ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ≤ 1
            · have hpow :
                ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ 1 := by
                have hpow' :
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                      ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ 0 :=
                  pow_le_pow_of_le_one (norm_nonneg _) hle (Nat.zero_le _)
                simpa using hpow'
              exact hpow.trans (le_max_left _ _)
            · have hlt : 1 < ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                lt_of_not_ge hle
              have hle1 : (1 : ℝ) ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                le_of_lt hlt
              have hpow :
                  ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ (k' + 1) := by
                have hnonneg : 0 ≤ ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' :=
                  pow_nonneg (norm_nonneg _) _
                have hmul :
                    ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤
                      ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' *
                        ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ :=
                  le_mul_of_one_le_right hnonneg hle1
                simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul
              have hpow' :
                  ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k' ≤ C :=
                hpow.trans (hC x)
              exact hpow'.trans (le_max_right _ _)
          refine ⟨|M| * C', ?_⟩
          intro ω
          have hcomm :
              TestForm.pullbackToSmooth (n := n) (f := f) hf
                  (TestForm.smoothExtDeriv ω) =
                smoothExtDeriv (TestForm.pullbackToSmooth (n := n) (k := k') f hf ω) := by
            simpa using
              (TestForm.pullbackToSmooth_smoothExtDeriv (n := n) (k := k')
                (f := f) hf ω)
          have hT :
              |T.toFun (smoothExtDeriv
                  (TestForm.pullbackToSmooth (n := n) (k := k') f hf ω))| ≤
                M * ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ :=
            hM (TestForm.pullbackToSmooth (n := n) (k := k') f hf ω)
          have hMle :
              M * ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ ≤
                |M| * ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ := by
            have hnorm_nonneg :
                0 ≤ ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ :=
              norm_nonneg _
            exact mul_le_mul_of_nonneg_right (le_abs_self M) hnorm_nonneg
          have hnorm :
              ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ ≤
                TestForm.comass ω * C' := by
            exact
              TestForm.pullbackToSmooth_norm_le (n := n) (k := k')
                (f := f) hf (C := C') hC' ω
          have habs :
              |M| * ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ ≤
                |M| * (TestForm.comass ω * C') :=
            mul_le_mul_of_nonneg_left hnorm (abs_nonneg M)
          calc
            |T.toFun
                (TestForm.pullbackToSmooth (n := n) (k := k' + 1) f hf
                  (TestForm.smoothExtDeriv ω))| =
                |T.toFun (smoothExtDeriv
                  (TestForm.pullbackToSmooth (n := n) (k := k') f hf ω))| := by
                  rw [hcomm]
            _ ≤ |M| * ‖TestForm.pullbackToSmooth (n := n) (k := k') f hf ω‖ := hT.trans hMle
            _ ≤ |M| * (TestForm.comass ω * C') := habs
            _ = |M| * C' * TestForm.comass ω := by ring }

theorem currentPushforward_congr (f g : X → Y) (hfg : f = g)
    (C D : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (hD : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) g x‖ ^ k ≤ D)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (hg : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ g)
    (T : Current n X k) :
    currentPushforward (n := n) (k := k) (f := f) C hC hf T =
      currentPushforward (n := n) (k := k) (f := g) D hD hg T := by
  subst hfg
  apply LocalCurrent.ext
  intro ω
  change T.toFun (TestForm.pullbackToSmooth (n := n) (k := k) f hf ω) =
    T.toFun (TestForm.pullbackToSmooth (n := n) (k := k) f hg ω)
  rw [Hodge.TestForm.pullbackToSmooth_congr (n := n) (k := k) (f := f) (g := f) rfl hf hg ω]

@[simp] theorem currentPushforward_zero (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f) :
    currentPushforward (n := n) (k := k) (f := f) C hC hf (0 : Current n X k) = 0 := by
  ext ω
  change (0 : Current n X k).toFun
      (TestForm.pullbackToSmooth (n := n) (k := k) (f := f) hf ω) = 0
  simpa using
    (Current.zero_toFun (n := n) (X := X) (k := k)
      (ω := TestForm.pullbackToSmooth (n := n) (k := k) (f := f) hf ω))

theorem currentPushforward_isCycleAt (f : X → Y) (C : ℝ)
    (hC : ∀ x, ‖mfderiv (𝓒_complex n) (𝓒_complex n) f x‖ ^ k ≤ C)
    (hf : ContMDiff (𝓒_complex n) (𝓒_complex n) ⊤ f)
    (T : Current n X k) (hT : T.isCycleAt) :
    (currentPushforward (n := n) (k := k) (f := f) C hC hf T).isCycleAt := by
  cases k with
  | zero =>
      trivial
  | succ k' =>
      have hcycle : Current.boundary T = 0 := by
        simpa [Current.isCycleAt] using hT
      rw [LocalCurrent.isCycleAt_succ_iff]
      ext ω
      have hcomm :
          TestForm.pullbackToSmooth (n := n) (k := k' + 1) (f := f) hf
              (Hodge.TestForm.smoothExtDeriv ω) =
            _root_.smoothExtDeriv
              (TestForm.pullbackToSmooth (n := n) (k := k') (f := f) hf ω) := by
        simpa using
          (Hodge.TestForm.pullbackToSmooth_smoothExtDeriv (n := n) (k := k') (f := f) hf ω)
      calc
        (LocalCurrent.boundary
            (currentPushforward (n := n) (k := k' + 1) (f := f) C hC hf T)).toLinear ω
            = T.toFun
                (TestForm.pullbackToSmooth (n := n) (k := k' + 1) (f := f) hf
                  (Hodge.TestForm.smoothExtDeriv ω)) := rfl
        _ = T.toFun
              (_root_.smoothExtDeriv
                (TestForm.pullbackToSmooth (n := n) (k := k') (f := f) hf ω)) := by
              rw [hcomm]
        _ = (Current.boundary T).toFun
              (TestForm.pullbackToSmooth (n := n) (k := k') (f := f) hf ω) := by
              rw [Current.boundary_toFun]
        _ = 0 := by
              rw [hcycle]
              simpa using
                (Current.zero_toFun (n := n) (X := X) (k := k')
                  (ω := TestForm.pullbackToSmooth (n := n) (k := k') (f := f) hf ω))

end Hodge.GMT
