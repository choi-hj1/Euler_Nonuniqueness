import EulerNonuniqueness.Section3.ContourTangentInnerDerivative
import EulerNonuniqueness.Section3.ContourQuotientJetUniform

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourTangentInnerLinearBound (radius : ℝ) : ℝ :=
  contourCauchyParameterOperatorConstant radius * contourTangentQuotientConstant radius +
    (contourCauchyUniformOperatorConstant radius + Real.pi) * contourTangentQuotientLipschitzConstant radius

theorem contourTangentInnerLinear_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ < radius) :
    ‖contourTangentInnerLinear data increment‖ ≤ contourTangentInnerLinearBound radius * ‖increment‖ := by
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg nonnegative small
  have uniform_nonnegative := contourCauchyUniformOperatorConstant_nonneg nonnegative small
  have quotient_bound := extendedContourTangentQuotient_uniform_norm_bound data nonnegative small nearby.le
  have linear_bound := contourQuotientDerivative_uniform_norm_bound data increment nonnegative small nearby.le
  have first_bound : ‖contourCauchyDirectionalDerivative data increment (extendedContourTangentQuotient data)‖ ≤
      (contourCauchyParameterOperatorConstant radius * contourTangentQuotientConstant radius) * ‖increment‖ :=
    (contourCauchyDirectionalDerivative_norm_bound data increment _ nearby small).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left quotient_bound parameter_nonnegative)
        (norm_nonneg increment))
  have second_bound : ‖extendedContourCauchy data (contourQuotientDerivativeCLM data increment)‖ ≤
      (contourCauchyUniformOperatorConstant radius * contourTangentQuotientLipschitzConstant radius) * ‖increment‖ :=
    (extendedContourCauchy_uniform_norm_bound data _ nonnegative small nearby.le).trans
      ((mul_le_mul_of_nonneg_left linear_bound uniform_nonnegative).trans_eq (by ring))
  have third_bound : ‖((Real.pi : ℂ) * Complex.I) • (contourQuotientDerivativeCLM data increment)‖ ≤
      (Real.pi * contourTangentQuotientLipschitzConstant radius) * ‖increment‖ := by
    rw [norm_smul ((Real.pi : ℂ) * Complex.I) (contourQuotientDerivativeCLM data increment)]
    have scalar_norm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [scalar_norm]
    exact (mul_le_mul_of_nonneg_left linear_bound Real.pi_pos.le).trans_eq (by ring)
  exact (norm_add_le_of_le (norm_add_le_of_le first_bound second_bound) third_bound).trans_eq
    (by unfold contourTangentInnerLinearBound; ring)

end

end EulerNonuniqueness.Paper
