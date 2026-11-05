import EulerNonuniqueness.General.FlatDerivativeBound

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric Filter
open scoped Topology

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem exists_local_derivative_linear_bound_of_contDiffAt_two
    (function : Domain → Range) (smooth : ContDiffAt ℝ 2 function (0 : Domain))
    (flat : fderiv ℝ function (0 : Domain) = 0) :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ value ∈ closedBall (0 : Domain) radius, HasFDerivAt function (fderiv ℝ function value) value) ∧
      ∀ value ∈ closedBall (0 : Domain) radius, ‖fderiv ℝ function value‖ ≤ constant * ‖value‖ := by
  have derivativeSmooth : ContDiffAt ℝ 1 (fderiv ℝ function) (0 : Domain) :=
    smooth.fderiv_right (by norm_num)
  obtain ⟨constant, neighborhood, nearby, lipschitz⟩ := derivativeSmooth.exists_lipschitzOnWith
  have smoothNearby := smooth.eventually (by norm_num)
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp (inter_mem nearby smoothNearby)
  have subset : closedBall (0 : Domain) (radius / 2) ⊆ Metric.ball (0 : Domain) radius := by
    intro value member
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp member).trans_lt (by linarith)
  refine ⟨radius / 2, by positivity, (constant : ℝ), constant.coe_nonneg, ?_, ?_⟩
  · intro value member
    have localSmooth : ContDiffAt ℝ 2 function value := (contained (subset member)).2
    exact (localSmooth.differentiableAt (by decide)).hasFDerivAt
  · intro value member
    have actual := lipschitz.norm_sub_le (contained (subset member)).1 (mem_of_mem_nhds nearby)
    simpa only [flat, sub_zero] using actual

theorem exists_local_derivative_quadratic_bound_of_contDiffAt_three
    (function : Domain → Range) (smooth : ContDiffAt ℝ 3 function (0 : Domain))
    (flat : fderiv ℝ function (0 : Domain) = 0)
    (secondFlat : fderiv ℝ (fderiv ℝ function) (0 : Domain) = 0) :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ value ∈ closedBall (0 : Domain) radius, HasFDerivAt function (fderiv ℝ function value) value) ∧
      ∀ value ∈ closedBall (0 : Domain) radius, ‖fderiv ℝ function value‖ ≤ constant * ‖value‖ ^ 2 := by
  have derivativeSmooth : ContDiffAt ℝ 2 (fderiv ℝ function) (0 : Domain) :=
    smooth.fderiv_right (by norm_num)
  obtain ⟨radius, positive, constant, nonnegative, actual, estimate⟩ :=
    exists_local_derivative_linear_bound_of_contDiffAt_two (fderiv ℝ function) derivativeSmooth secondFlat
  obtain ⟨firstRadius, firstPositive, firstConstant, firstNonnegative, firstActual, firstEstimate⟩ :=
    exists_local_derivative_linear_bound_of_contDiffAt_two function (smooth.of_le (by decide)) flat
  refine ⟨min radius firstRadius, lt_min positive firstPositive, constant, nonnegative, ?_, ?_⟩
  · intro value member
    exact firstActual value (mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp member).trans (min_le_right _ _)))
  · intro value inside
    have contained : closedBall (0 : Domain) ‖value‖ ⊆ closedBall (0 : Domain) radius := by
      intro point member
      exact mem_closedBall_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp member).trans
          ((mem_closedBall_zero_iff.mp inside).trans (min_le_left _ _)))
    have bound := (convex_closedBall (0 : Domain) ‖value‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun point member => (actual point (contained member)).hasFDerivWithinAt)
      (fun point member => (estimate point (contained member)).trans
        (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp member) nonnegative))
      (mem_closedBall_self (norm_nonneg value))
      (mem_closedBall_zero_iff.mpr (le_refl ‖value‖))
    simpa only [flat, sub_zero, ← pow_two, mul_assoc] using bound

theorem exists_local_derivative_quadratic_bound_of_contDiff_three
    (function : Domain → Range) (smooth : ContDiff ℝ 3 function)
    (flat : fderiv ℝ function (0 : Domain) = 0)
    (secondFlat : fderiv ℝ (fderiv ℝ function) (0 : Domain) = 0) :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ value ∈ closedBall (0 : Domain) radius, HasFDerivAt function (fderiv ℝ function value) value) ∧
      ∀ value ∈ closedBall (0 : Domain) radius, ‖fderiv ℝ function value‖ ≤ constant * ‖value‖ ^ 2 := by
  have derivativeSmooth : ContDiff ℝ 2 (fderiv ℝ function) := smooth.fderiv_right (by norm_num)
  obtain ⟨radius, positive, constant, nonnegative, actual, estimate⟩ :=
    exists_local_derivative_linear_bound_of_contDiff_two (fderiv ℝ function) derivativeSmooth secondFlat
  refine ⟨radius, positive, constant, nonnegative, ?_, ?_⟩
  · intro value _member
    exact (smooth.differentiable (by norm_num) value).hasFDerivAt
  · intro value inside
    have contained : closedBall (0 : Domain) ‖value‖ ⊆ closedBall (0 : Domain) radius := by
      intro point member
      exact mem_closedBall_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp member).trans (mem_closedBall_zero_iff.mp inside))
    have bound := (convex_closedBall (0 : Domain) ‖value‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun point member => (actual point (contained member)).hasFDerivWithinAt)
      (fun point member => (estimate point (contained member)).trans
        (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp member) nonnegative))
      (mem_closedBall_self (norm_nonneg value))
      (mem_closedBall_zero_iff.mpr (le_refl ‖value‖))
    simpa only [flat, sub_zero, ← pow_two, mul_assoc] using bound

end

end EulerNonuniqueness.General
