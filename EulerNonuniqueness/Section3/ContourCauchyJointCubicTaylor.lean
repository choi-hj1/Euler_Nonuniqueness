import EulerNonuniqueness.Section3.ContourCauchyCubicTaylor
import EulerNonuniqueness.Section3.ContourCauchyJointDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchy_joint_cubic_taylor_bound
    (data increment : PeriodicC1HolderHalf) (density densityIncrement : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchy (data + increment) (density + densityIncrement) -
        extendedContourCauchy data density -
        (contourCauchyDirectionalDerivative data increment density +
          extendedContourCauchy data densityIncrement) -
        ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density +
          contourCauchyDirectionalDerivative data increment densityIncrement)‖ ≤
      (16 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 +
      (8 * (contourCauchyUniformOperatorConstant radius * ‖densityIncrement‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
  have nearby : ‖data + increment - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have identity : data + increment - standardCircleBanach =
        (data - standardCircleBanach) + increment := by abel
    have bound : ‖data + increment - standardCircleBanach‖ ≤ radius := by
      rw [identity]
      exact (norm_add_le (data - standardCircleBanach) increment).trans (by linarith)
    exact bound.trans_lt small
  rw [extendedContourCauchy_add_density _ _ _ nearby]
  have identity :
      extendedContourCauchy (data + increment) density +
          extendedContourCauchy (data + increment) densityIncrement -
        extendedContourCauchy data density -
        (contourCauchyDirectionalDerivative data increment density +
          extendedContourCauchy data densityIncrement) -
        ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density +
          contourCauchyDirectionalDerivative data increment densityIncrement) =
      (extendedContourCauchy (data + increment) density - extendedContourCauchy data density -
        contourCauchyDirectionalDerivative data increment density -
        (1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density) +
      (extendedContourCauchy (data + increment) densityIncrement -
        extendedContourCauchy data densityIncrement -
        contourCauchyDirectionalDerivative data increment densityIncrement) := by abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add
    (contourCauchy_cubic_taylor_bound data increment density near small increment_small)
    (contourCauchy_quadratic_remainder_bound data increment densityIncrement near small increment_small))

end

end EulerNonuniqueness.Paper
