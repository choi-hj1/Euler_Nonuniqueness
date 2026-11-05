import Mathlib

noncomputable section

open Filter
open scoped Topology InnerProductSpace

theorem tendsto_inner_of_weak_of_strong
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    {filter : Filter Index} {sequence tests : Index → Hilbert} {limit test : Hilbert} {bound : ℝ}
    (bounded : ∀ index, ‖sequence index‖ ≤ bound)
    (weak : ∀ fixed : Hilbert,
      Tendsto (fun index => ⟪sequence index, fixed⟫_ℝ) filter (𝓝 ⟪limit, fixed⟫_ℝ))
    (strong : Tendsto tests filter (𝓝 test)) :
    Tendsto (fun index => ⟪sequence index, tests index⟫_ℝ) filter (𝓝 ⟪limit, test⟫_ℝ) := by
  have normDifference : Tendsto (fun index => ‖tests index - test‖) filter (𝓝 0) := by
    simpa only [sub_self, norm_zero] using
      (strong.sub (tendsto_const_nhds (x := test))).norm
  have errorBound (index : Index) :
      ‖⟪sequence index, tests index - test⟫_ℝ‖ ≤ max bound 0 * ‖tests index - test‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right ((bounded index).trans (le_max_left bound 0)) (norm_nonneg _))
  have error : Tendsto (fun index => ⟪sequence index, tests index - test⟫_ℝ)
      filter (𝓝 0) := by
    apply squeeze_zero_norm errorBound
    simpa only [mul_zero] using normDifference.const_mul (max bound 0)
  have expansion (index : Index) :
      ⟪sequence index, tests index - test⟫_ℝ + ⟪sequence index, test⟫_ℝ =
        ⟪sequence index, tests index⟫_ℝ := by rw [inner_sub_right]; ring
  simpa only [zero_add, expansion] using error.add (weak test)

theorem continuous_inner_of_weak_of_strong
    {Hilbert Parameter : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [TopologicalSpace Parameter] {sequence tests : Parameter → Hilbert} {bound : ℝ}
    (bounded : ∀ parameter, ‖sequence parameter‖ ≤ bound)
    (weak : ∀ fixed : Hilbert, Continuous (fun parameter => ⟪sequence parameter, fixed⟫_ℝ))
    (strong : Continuous tests) : Continuous (fun parameter => ⟪sequence parameter, tests parameter⟫_ℝ) := by
  apply continuous_iff_continuousAt.mpr
  intro parameter
  exact tendsto_inner_of_weak_of_strong bounded
    (fun fixed => (weak fixed).tendsto parameter) (strong.tendsto parameter)
