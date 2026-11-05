import EulerNonuniqueness.Section3.HolderWeakHolomorphic
import EulerNonuniqueness.Section3.ContourCauchyParameterDifferentiation
import EulerNonuniqueness.Section3.ContourCauchyLipschitz

open Set Metric Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def extendedContourCauchy (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf) : PeriodicHolderHalf := by
  classical
  exact if small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) then
    contourCauchyOperator data small density else 0

theorem extendedContourCauchy_eq (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchy data density = contourCauchyOperator data small density := by
  classical
  simp only [extendedContourCauchy, dif_pos small]

theorem contourCauchyTransform_differentiableAt_complex_parameter (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • direction - standardCircleBanach‖ < 2 / (3 * Real.pi)) (target : ℝ) :
    DifferentiableAt ℂ (fun current : ℂ => contourCauchyTransform (data + current • direction).val.1
      (data + current • direction).val.2.val.1 density.val.1 target) parameter := by
  obtain ⟨radius, near, smaller⟩ := exists_between small
  have derivative := contourCauchyTransform_hasDerivAt_complex_parameter
    (data + parameter • direction) direction density near smaller target
  have outer : DifferentiableAt ℂ (fun current : ℂ => contourCauchyTransform
      (data + parameter • direction + current • direction).val.1
      (data + parameter • direction + current • direction).val.2.val.1 density.val.1 target)
      (parameter - parameter) := by simpa only [sub_self] using derivative.differentiableAt
  have inner : DifferentiableAt ℂ (fun current : ℂ => current - parameter) parameter :=
    differentiableAt_id.sub (differentiableAt_const parameter)
  have translated := outer.comp (f := fun current : ℂ => current - parameter) parameter inner
  convert translated using 1
  ext current
  dsimp only [Function.comp_apply]
  have identity : data + parameter • direction + (current - parameter) • direction = data + current • direction := by
    rw [sub_smul current parameter direction]
    abel
  rw [identity]

theorem extendedContourCauchy_continuousOn_complex_line (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) {domain : Set ℂ} {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (near : ∀ parameter ∈ domain, ‖data + parameter • direction - standardCircleBanach‖ ≤ radius) :
    ContinuousOn (fun parameter : ℂ => extendedContourCauchy (data + parameter • direction) density) domain := by
  let constant : ℝ := contourCauchyParameterOperatorConstant radius * ‖direction‖ * ‖density‖
  have constant_nonnegative : 0 ≤ constant := by
    have bound_nonnegative := contourCauchyParameterSupConstant_nonneg nonnegative small
    have operator_nonnegative : 0 ≤ contourCauchyParameterOperatorConstant radius :=
      bound_nonnegative.trans (le_max_left _ _)
    exact mul_nonneg (mul_nonneg operator_nonnegative (norm_nonneg _)) (norm_nonneg _)
  apply (LipschitzOnWith.of_dist_le_mul (K := ⟨constant, constant_nonnegative⟩) ?_).continuousOn
  intro first first_member second second_member
  rw [extendedContourCauchy_eq _ _ ((near first first_member).trans_lt small),
    extendedContourCauchy_eq _ _ ((near second second_member).trans_lt small), dist_eq_norm, dist_eq_norm]
  have bound := contourCauchyOperator_parameter_norm_bound (data + first • direction)
    (data + second • direction) density nonnegative small (near first first_member) (near second second_member)
  have difference : data + first • direction - (data + second • direction) = (first - second) • direction := by
    rw [sub_smul first second direction]
    abel
  rw [difference, norm_smul (first - second) direction] at bound
  exact bound.trans_eq (by change _ = constant * ‖first - second‖; dsimp only [constant]; ring)

theorem extendedContourCauchy_differentiableAt_evaluation (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf) (parameter : ℂ)
    (small : ‖data + parameter • direction - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (target : ℝ) : DifferentiableAt ℂ
      (fun current : ℂ => (extendedContourCauchy (data + current • direction) density).val.1 target) parameter := by
  have actual := contourCauchyTransform_differentiableAt_complex_parameter data direction density parameter
    (small.trans_le (min_le_right _ _)) target
  apply actual.congr_of_eventuallyEq
  have path : LipschitzWith ⟨‖direction‖, norm_nonneg direction⟩
      (fun current : ℂ => data + current • direction - standardCircleBanach) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    rw [dist_eq_norm (data + first • direction - standardCircleBanach)
      (data + second • direction - standardCircleBanach), dist_eq_norm first second]
    have identity : data + first • direction - standardCircleBanach -
        (data + second • direction - standardCircleBanach) = (first - second) • direction := by
      rw [sub_smul first second direction]
      abel
    rw [identity, norm_smul (first - second) direction]
    exact le_of_eq (mul_comm _ _)
  have continuity : Continuous (fun current : ℂ => ‖data + current • direction - standardCircleBanach‖) :=
    path.continuous.norm
  filter_upwards [continuity.continuousAt.eventually (gt_mem_nhds small)] with current nearby
  rw [extendedContourCauchy_eq _ _ nearby, contourCauchyOperator_value]

theorem analyticAt_extendedContourCauchy_complex_line (data direction : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    AnalyticAt ℂ (fun parameter : ℂ => extendedContourCauchy (data + parameter • direction) density) 0 := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  let parameter_radius : ℝ := (radius - ‖data - standardCircleBanach‖) / (2 * (‖direction‖ + 1))
  have parameter_positive : 0 < parameter_radius := div_pos (sub_pos.mpr near) (by positivity)
  have nearby (parameter : ℂ) (member : parameter ∈ closedBall 0 parameter_radius) :
      ‖data + parameter • direction - standardCircleBanach‖ < radius := by
    apply complexContourPerturbation_near data direction near
    have member_bound : ‖parameter‖ ≤ parameter_radius := by simpa only [mem_closedBall, dist_zero_right] using member
    apply member_bound.trans_lt
    dsimp only [parameter_radius]
    have denominator_positive : 0 < ‖direction‖ + 1 := by positivity
    have difference_positive := sub_pos.mpr near
    exact div_lt_div_of_pos_left difference_positive denominator_positive (by linarith)
  apply analyticAt_holderCurve_of_evaluations (radius := ⟨parameter_radius, parameter_positive.le⟩) parameter_positive
  · exact extendedContourCauchy_continuousOn_complex_line data direction density
      ((norm_nonneg _).trans near.le) radius_small (fun parameter member => (nearby parameter member).le)
  · intro target parameter member
    exact (extendedContourCauchy_differentiableAt_evaluation data direction density parameter
      ((nearby parameter (ball_subset_closedBall member)).trans radius_small) target).differentiableWithinAt

end

end EulerNonuniqueness.Paper
