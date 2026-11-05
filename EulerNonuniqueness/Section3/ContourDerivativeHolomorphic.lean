import EulerNonuniqueness.Section3.ContourDerivativeScalarHolomorphic
import EulerNonuniqueness.Section3.ContourCauchyDerivativeLipschitz

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchyDirectionalDerivative_continuousOn_complex_line
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {domain : Set ℂ} {innerRadius outerRadius : ℝ}
    (inner_nonnegative : 0 ≤ innerRadius) (gap : innerRadius < outerRadius)
    (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ∀ parameter ∈ domain,
      ‖data + parameter • second - standardCircleBanach‖ ≤ innerRadius) :
    ContinuousOn (fun parameter : ℂ =>
      contourCauchyDirectionalDerivative (data + parameter • second) first density) domain := by
  let auxiliaryRadius : ℝ≥0 := ⟨(outerRadius - innerRadius) / (‖first‖ + 1),
    div_nonneg (sub_nonneg.mpr gap.le) (by positivity)⟩
  have positive : 0 < auxiliaryRadius := div_pos (sub_pos.mpr gap) (by positivity)
  let constant := contourCauchyParameterOperatorConstant outerRadius * ‖second‖ * ‖density‖ /
    (auxiliaryRadius : ℝ)
  have operator_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant outerRadius :=
    (contourCauchyParameterSupConstant_nonneg (inner_nonnegative.trans gap.le) small).trans
      (le_max_left _ _)
  have constant_nonnegative : 0 ≤ constant :=
    div_nonneg (mul_nonneg (mul_nonneg operator_nonnegative (norm_nonneg _)) (norm_nonneg _))
      auxiliaryRadius.coe_nonneg
  have perturbed_near (parameter : ℂ) (member : parameter ∈ domain)
      (auxiliary : ℂ) (auxiliary_member : auxiliary ∈ closedBall (0 : ℂ) auxiliaryRadius) :
      ‖data + parameter • second + auxiliary • first - standardCircleBanach‖ ≤ outerRadius := by
    have auxiliary_bound : ‖auxiliary‖ ≤ (outerRadius - innerRadius) / (‖first‖ + 1) := by
      simpa only [mem_closedBall, dist_zero_right] using auxiliary_member
    have product_bound := (le_div_iff₀ (by positivity : (0 : ℝ) < ‖first‖ + 1)).mp auxiliary_bound
    exact (complexContourPerturbation_distance (data + parameter • second) first auxiliary).trans
      (by have initial := nearby parameter member; nlinarith [norm_nonneg auxiliary])
  apply (LipschitzOnWith.of_dist_le_mul (K := ⟨constant, constant_nonnegative⟩) ?_).continuousOn
  intro initial initial_member final final_member
  rw [dist_eq_norm, dist_eq_norm initial final]
  have estimate := contourCauchyDirectionalDerivative_difference_bound
    (data + initial • second) (data + final • second) first density
    (inner_nonnegative.trans gap.le) small positive
    (perturbed_near initial initial_member) (perturbed_near final final_member)
  have difference : data + initial • second - (data + final • second) =
      (initial - final) • second := by
    rw [sub_smul initial final second]
    abel
  rw [difference, norm_smul (initial - final) second] at estimate
  exact estimate.trans_eq (by change _ = constant * ‖initial - final‖; dsimp only [constant]; ring)

theorem analyticAt_contourCauchyDirectionalDerivative_complex_line
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    AnalyticAt ℂ (fun parameter : ℂ =>
      contourCauchyDirectionalDerivative (data + parameter • second) first density) 0 := by
  obtain ⟨innerRadius, near, inner_small⟩ := exists_between small
  obtain ⟨outerRadius, gap, outer_small⟩ := exists_between inner_small
  let parameterRadius := (innerRadius - ‖data - standardCircleBanach‖) /
    (2 * (‖second‖ + 1))
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr near) (by positivity)
  have nearby (parameter : ℂ) (member : parameter ∈ closedBall (0 : ℂ) parameterRadius) :
      ‖data + parameter • second - standardCircleBanach‖ < innerRadius := by
    apply complexContourPerturbation_near data second near
    have parameter_bound : ‖parameter‖ ≤ parameterRadius := by
      simpa only [mem_closedBall, dist_zero_right] using member
    apply parameter_bound.trans_lt
    dsimp only [parameterRadius]
    exact div_lt_div_of_pos_left (sub_pos.mpr near) (by positivity)
      (by nlinarith [norm_nonneg second])
  apply analyticAt_holderCurve_of_evaluations
    (radius := ⟨parameterRadius, positive.le⟩) positive
  · exact contourCauchyDirectionalDerivative_continuousOn_complex_line data first second density
      ((norm_nonneg _).trans near.le) gap outer_small
      (fun parameter member => (nearby parameter member).le)
  · intro target parameter member
    exact (contourCauchyDirectionalDerivative_evaluation_differentiableAt data first second density
      parameter ((nearby parameter (ball_subset_closedBall member)).trans inner_small)
      target).differentiableWithinAt

end

end EulerNonuniqueness.Paper
