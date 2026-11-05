import EulerNonuniqueness.General.BoundedLipschitzODE

noncomputable section

open Set Metric
open scoped NNReal

theorem exists_solution_Icc_of_bounded_timeDependent_lipschitz
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {field : ℝ → Space → Space} {lipschitzBound speedBound : ℝ≥0} {horizon : ℝ}
    (nonnegative : 0 ≤ horizon)
    (lipschitz : ∀ time ∈ Icc 0 horizon, LipschitzWith lipschitzBound (field time))
    (continuous : ∀ state, ContinuousOn (fun time => field time state) (Icc 0 horizon))
    (bounded : ∀ time ∈ Icc 0 horizon, ∀ state, ‖field time state‖ ≤ speedBound) (initial : Space) :
    ∃ path : ℝ → Space, path 0 = initial ∧ ContinuousOn path (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, HasDerivWithinAt path (field time (path time)) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon, ‖path time - initial‖ ≤ speedBound * time := by
  have hypotheses : IsPicardLindelof field 0 0 horizon initial lipschitzBound (speedBound * horizon) speedBound := by
    refine ⟨⟨le_rfl, nonnegative⟩, mul_nonneg speedBound.coe_nonneg nonnegative,
      fun time inside => (lipschitz time inside).lipschitzOnWith, fun state _ => continuous state,
      fun time inside state _ => bounded time inside state, ?_⟩
    simp only [sub_zero, sub_self, max_eq_left nonnegative, le_refl]
  obtain ⟨path, initialEquality, derivative⟩ := hypotheses.exists_forall_hasDerivWithinAt_Icc_eq initial
  have pathContinuous : ContinuousOn path (Icc 0 horizon) := fun time inside => (derivative time inside).continuousWithinAt
  have pathLipschitz : LipschitzOnWith speedBound path (Icc 0 horizon) :=
    (convex_Icc 0 horizon).lipschitzOnWith_of_nnnorm_hasDerivWithin_le derivative
      (fun time inside => by exact_mod_cast bounded time inside (path time))
  refine ⟨path, initialEquality, pathContinuous, derivative, fun time inside => ?_⟩
  have estimate := pathLipschitz.dist_le_mul time inside 0 ⟨le_rfl, nonnegative⟩
  simpa only [dist_eq_norm, initialEquality, Real.norm_eq_abs, sub_zero, abs_of_nonneg inside.1] using estimate
