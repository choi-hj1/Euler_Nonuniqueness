import EulerNonuniqueness.Section3.ContourCauchyJointCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourCauchy_density_jet_remainder_identity
    (data increment : PeriodicC1HolderHalf)
    (density densityLinear densityQuadratic densityNext : PeriodicHolderHalf)
    (small : ‖data + increment - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchy (data + increment) densityNext - extendedContourCauchy data density -
        (contourCauchyDirectionalDerivative data increment density +
          extendedContourCauchy data densityLinear) -
        ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density +
          contourCauchyDirectionalDerivative data increment densityLinear +
          extendedContourCauchy data densityQuadratic) =
      (extendedContourCauchy (data + increment) density - extendedContourCauchy data density -
        contourCauchyDirectionalDerivative data increment density -
        (1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density) +
      (extendedContourCauchy (data + increment) densityLinear -
        extendedContourCauchy data densityLinear -
        contourCauchyDirectionalDerivative data increment densityLinear) +
      (extendedContourCauchy (data + increment) densityQuadratic -
        extendedContourCauchy data densityQuadratic) +
      extendedContourCauchy (data + increment)
        (densityNext - density - densityLinear - densityQuadratic) := by
  have density_identity : densityNext =
      ((density + densityLinear) + densityQuadratic) +
        (densityNext - density - densityLinear - densityQuadratic) := by abel
  conv_lhs => lhs; lhs; lhs; rw [density_identity]
  rw [extendedContourCauchy_add_density _ _ _ small,
    extendedContourCauchy_add_density _ _ _ small,
    extendedContourCauchy_add_density _ _ _ small]
  abel

theorem contourCauchy_density_jet_remainder_bound
    (data increment : PeriodicC1HolderHalf)
    (density densityLinear densityQuadratic densityNext : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchy (data + increment) densityNext - extendedContourCauchy data density -
        (contourCauchyDirectionalDerivative data increment density +
          extendedContourCauchy data densityLinear) -
        ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density +
          contourCauchyDirectionalDerivative data increment densityLinear +
          extendedContourCauchy data densityQuadratic)‖ ≤
      (16 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 +
      (8 * (contourCauchyUniformOperatorConstant radius * ‖densityLinear‖) /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 +
      contourCauchyParameterOperatorConstant radius * ‖increment‖ * ‖densityQuadratic‖ +
      contourCauchyUniformOperatorConstant radius *
        ‖densityNext - density - densityLinear - densityQuadratic‖ := by
  have nonnegative : 0 ≤ radius := (norm_nonneg _).trans near.le
  have nearby : ‖data + increment - standardCircleBanach‖ ≤ radius := by
    have identity : data + increment - standardCircleBanach =
        (data - standardCircleBanach) + increment := by abel
    rw [identity]
    exact (norm_add_le (data - standardCircleBanach) increment).trans (by linarith)
  have mixed_bound : ‖extendedContourCauchy (data + increment) densityQuadratic -
      extendedContourCauchy data densityQuadratic‖ ≤
      contourCauchyParameterOperatorConstant radius * ‖increment‖ * ‖densityQuadratic‖ := by
    rw [extendedContourCauchy_eq _ _ (nearby.trans_lt small),
      extendedContourCauchy_eq _ _ (near.trans small)]
    have result := contourCauchyOperator_parameter_norm_bound (data + increment) data densityQuadratic
      nonnegative small nearby near.le
    have identity : data + increment - data = increment := by abel
    rwa [identity] at result
  rw [contourCauchy_density_jet_remainder_identity _ _ _ _ _ _ (nearby.trans_lt small)]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (norm_add_le _ _).trans (add_le_add
        (contourCauchy_cubic_taylor_bound data increment density near small increment_small)
        (contourCauchy_quadratic_remainder_bound data increment densityLinear near small increment_small))
    · exact mixed_bound
  · exact extendedContourCauchy_uniform_norm_bound _ _ nonnegative small nearby

end

end EulerNonuniqueness.Paper
