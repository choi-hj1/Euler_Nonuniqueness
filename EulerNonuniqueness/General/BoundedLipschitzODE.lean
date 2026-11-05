import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set Metric
open scoped NNReal

theorem exists_solution_Icc_of_bounded_lipschitz
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {field : Space → Space} {lipschitzBound speedBound : ℝ≥0}
    (lipschitz : LipschitzWith lipschitzBound field) (bounded : ∀ state, ‖field state‖ ≤ speedBound)
    (initial : Space) {horizon : ℝ} (nonnegative : 0 ≤ horizon) :
    ∃ path : ℝ → Space, path 0 = initial ∧ ContinuousOn path (Icc 0 horizon) ∧
      (∀ time ∈ Icc 0 horizon, HasDerivWithinAt path (field (path time)) (Icc 0 horizon) time) ∧
      ∀ time ∈ Icc 0 horizon, ‖path time - initial‖ ≤ speedBound * time := by
  have hypotheses : IsPicardLindelof (fun _ state => field state) 0 0 horizon initial lipschitzBound
      (speedBound * horizon) speedBound := by
    refine ⟨⟨le_rfl, nonnegative⟩, mul_nonneg speedBound.coe_nonneg nonnegative,
      fun _ _ => lipschitz.lipschitzOnWith, fun _ _ => continuousOn_const, fun _ _ state _ => bounded state, ?_⟩
    simp only [sub_zero, sub_self, max_eq_left nonnegative, le_refl]
  obtain ⟨path, initialEquality, derivative⟩ := hypotheses.exists_forall_hasDerivWithinAt_Icc_eq initial
  have continuous : ContinuousOn path (Icc 0 horizon) := fun time inside => (derivative time inside).continuousWithinAt
  have pathLipschitz : LipschitzOnWith speedBound path (Icc 0 horizon) :=
    (convex_Icc 0 horizon).lipschitzOnWith_of_nnnorm_hasDerivWithin_le derivative
      (fun time _ => by exact_mod_cast bounded (path time))
  refine ⟨path, initialEquality, continuous, derivative, fun time inside => ?_⟩
  have estimate := pathLipschitz.dist_le_mul time inside 0 ⟨le_rfl, nonnegative⟩
  simpa only [dist_eq_norm, initialEquality, Real.norm_eq_abs, sub_zero, abs_of_nonneg inside.1] using estimate
