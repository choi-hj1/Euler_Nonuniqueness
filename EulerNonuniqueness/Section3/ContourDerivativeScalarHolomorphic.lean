import EulerNonuniqueness.Section3.ContourVariationIntegralDerivative
import EulerNonuniqueness.Section3.ContourCauchyFrechet

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchyDirectionalDerivative_evaluation_hasDerivAt_zero
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (target : ℝ) :
    HasDerivAt (fun parameter : ℂ =>
      (contourCauchyDirectionalDerivative (data + parameter • second) first density).val.1 target)
      (2 * contourCauchyQuadraticIntegral data first second density target) 0 := by
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  have actual := contourCauchyVariationIntegral_hasDerivAt_parameter data first second density
    near (radius_small.trans_le (min_le_right _ _)) target
  apply actual.congr_of_eventuallyEq
  let parameterRadius := (radius - ‖data - standardCircleBanach‖) / (‖second‖ + 1)
  have positive : 0 < parameterRadius := div_pos (sub_pos.mpr near) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with parameter member
  have nearby : ‖data + parameter • second - standardCircleBanach‖ < radius := by
    apply complexContourPerturbation_near data second near
    simpa only [Metric.mem_ball, dist_zero_right, parameterRadius] using member
  exact contourCauchyDirectionalDerivative_value (data + parameter • second) first density
    (nearby.trans radius_small) target

theorem contourCauchyDirectionalDerivative_evaluation_differentiableAt
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (parameter : ℂ)
    (small : ‖data + parameter • second - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)))
    (target : ℝ) :
    DifferentiableAt ℂ (fun current : ℂ =>
      (contourCauchyDirectionalDerivative (data + current • second) first density).val.1 target)
      parameter := by
  have actual := (contourCauchyDirectionalDerivative_evaluation_hasDerivAt_zero
    (data + parameter • second) first second density small target).differentiableAt
  have outer : DifferentiableAt ℂ (fun current : ℂ =>
      (contourCauchyDirectionalDerivative (data + parameter • second + current • second)
        first density).val.1 target) (parameter - parameter) := by
    simpa only [sub_self] using actual
  have inner : DifferentiableAt ℂ (fun current : ℂ => current - parameter) parameter :=
    differentiableAt_id.sub (differentiableAt_const parameter)
  have translated := outer.comp (f := fun current : ℂ => current - parameter) parameter inner
  apply translated.congr_of_eventuallyEq
  filter_upwards [] with current
  dsimp only [Function.comp_apply]
  have identity : data + parameter • second + (current - parameter) • second =
      data + current • second := by
    rw [sub_smul current parameter second]
    abel
  rw [identity]

end

end EulerNonuniqueness.Paper
