import EulerNonuniqueness.Section6.FourPointCenterModes

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem contDiffAt_uniform_quadratic_remainder {Domain Value : Type*}
    [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {function : Domain → Value} {base : Domain} (smooth : ContDiffAt ℝ 2 function base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ center increment : Domain,
      ‖center - base‖ < radius → ‖increment‖ < radius →
      ‖function (center + increment) - function center - fderiv ℝ function center increment‖ ≤
        bound * ‖increment‖ ^ 2 := by
  obtain ⟨bound, neighborhood, neighborhoodMem, lipschitz⟩ :=
    (smooth.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  obtain ⟨radius, radiusPositive, ballInside⟩ := Metric.mem_nhds_iff.mp
    (inter_mem neighborhoodMem (smooth.eventually (by norm_num)))
  refine ⟨bound, bound.coe_nonneg, radius / 4, by positivity, ?_⟩
  intro center increment centerSmall incrementSmall
  have inside : Metric.closedBall center ‖increment‖ ⊆ neighborhood ∩
      {current | ContDiffAt ℝ 2 function current} := by
    intro current currentInside
    apply ballInside
    rw [Metric.mem_ball, dist_eq_norm]
    have currentBound : ‖current - center‖ ≤ ‖increment‖ := by
      simpa only [Metric.mem_closedBall, dist_eq_norm] using currentInside
    have triangle : ‖current - base‖ ≤ ‖current - center‖ + ‖center - base‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (current - center) (center - base)
    linarith
  have centerInside : center ∈ Metric.closedBall center ‖increment‖ := by simp
  have derivative : ∀ current ∈ Metric.closedBall center ‖increment‖,
      HasFDerivWithinAt (fun current => function current - function center - fderiv ℝ function center current)
        (fderiv ℝ function current - fderiv ℝ function center)
        (Metric.closedBall center ‖increment‖) current := by
    intro current currentInside
    have currentSmooth : ContDiffAt ℝ 2 function current := (inside currentInside).2
    simpa only [sub_zero] using (((currentSmooth.differentiableAt (by norm_num)).hasFDerivAt.sub
      (hasFDerivAt_const (function center) current)).sub
        (fderiv ℝ function center).hasFDerivAt).hasFDerivWithinAt
  have derivativeBound : ∀ current ∈ Metric.closedBall center ‖increment‖,
      ‖fderiv ℝ function current - fderiv ℝ function center‖ ≤ (bound : ℝ) * ‖increment‖ := by
    intro current currentInside
    exact ((lipschitzOnWith_iff_norm_sub_le.mp lipschitz) (inside currentInside).1 (inside centerInside).1).trans
      (mul_le_mul_of_nonneg_left
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using currentInside) bound.coe_nonneg)
  have endpointInside : center + increment ∈ Metric.closedBall center ‖increment‖ := by
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, le_refl]
  have estimate := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le derivative derivativeBound
    (convex_closedBall center ‖increment‖) centerInside endpointInside
  convert estimate using 1
  · congr 1
    rw [map_add]
    abel
  · simp only [add_sub_cancel_left, pow_two, mul_assoc]

theorem fourPointField_uniform_quadratic_remainder {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ center increment : FourPointConfiguration, FourPointNoncollision center →
      ‖center - base‖ < radius → ‖increment‖ < radius →
      ‖fourPointField coefficient (center + increment) - fourPointField coefficient center -
        fourPointLinearization coefficient center increment‖ ≤
        bound * |coefficient| * ‖increment‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    contDiffAt_uniform_quadratic_remainder (fourPointField_contDiffAt 1 noncollision)
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient center increment centerNoncollision centerSmall incrementSmall
  have unitEstimate := estimate center increment centerSmall incrementSmall
  rw [fourPointField_fderiv 1 centerNoncollision] at unitEstimate
  have scaled : fourPointField coefficient (center + increment) - fourPointField coefficient center -
      fourPointLinearization coefficient center increment =
      coefficient • (fourPointField 1 (center + increment) - fourPointField 1 center -
        fourPointLinearization 1 center increment) := by
    rw [fourPointField_scaling coefficient, fourPointField_scaling coefficient,
      fourPointLinearization_scaling coefficient, smul_sub, smul_sub]
  rw [scaled, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |coefficient| * (bound * ‖increment‖ ^ 2) :=
      mul_le_mul_of_nonneg_left unitEstimate (abs_nonneg coefficient)
    _ = _ := by ring

end EulerNonuniqueness.Section6
