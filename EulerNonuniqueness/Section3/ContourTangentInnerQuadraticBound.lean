import EulerNonuniqueness.Section3.ContourTangentInnerJet
import EulerNonuniqueness.Section3.ContourQuotientJetUniform

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourTangentInnerQuadraticBound (innerRadius outerRadius : ℝ) : ℝ :=
  4 * contourCauchyParameterOperatorConstant outerRadius * contourTangentQuotientConstant outerRadius /
      (outerRadius - innerRadius) +
    contourCauchyParameterOperatorConstant outerRadius * contourTangentQuotientLipschitzConstant outerRadius +
    (contourCauchyUniformOperatorConstant outerRadius + Real.pi) * contourQuotientQuadraticBound outerRadius

theorem contourTangentInnerQuadratic_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius) :
    ‖contourTangentInnerQuadratic data increment‖ ≤
      contourTangentInnerQuadraticBound innerRadius outerRadius * ‖increment‖ ^ 2 := by
  have outer_nonnegative := nonnegative.trans gap.le
  have outer_near := nearby.trans_lt gap
  have outer_near_le := outer_near.le
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg outer_nonnegative small
  have uniform_nonnegative := contourCauchyUniformOperatorConstant_nonneg outer_nonnegative small
  have quotient_bound := extendedContourTangentQuotient_uniform_norm_bound data outer_nonnegative small outer_near_le
  have quotient_linear_bound := contourQuotientDerivative_uniform_norm_bound data increment
    outer_nonnegative small outer_near_le
  have quotient_quadratic_bound : ‖contourQuotientQuadratic data increment‖ ≤
      contourQuotientQuadraticBound outerRadius * ‖increment‖ ^ 2 :=
    contourQuotientQuadratic_norm_bound data increment outer_nonnegative small outer_near_le
  have middle_near : ‖data - standardCircleBanach‖ < (innerRadius + outerRadius) / 2 := by linarith
  have middle_gap : (innerRadius + outerRadius) / 2 < outerRadius := by linarith
  have middle_nonnegative : 0 ≤ outerRadius - (innerRadius + outerRadius) / 2 := by linarith
  have second_bound := contourCauchySecondVariation_norm_bound data increment increment
    (extendedContourTangentQuotient data) middle_near middle_gap small
  have half_bound : ‖(1 / 2 : ℂ) • contourCauchySecondVariation data increment increment
      (extendedContourTangentQuotient data)‖ ≤
      (4 * contourCauchyParameterOperatorConstant outerRadius * contourTangentQuotientConstant outerRadius /
        (outerRadius - innerRadius)) * ‖increment‖ ^ 2 := by
    calc
      _ ≤ ‖contourCauchySecondVariation data increment increment
          (extendedContourTangentQuotient data)‖ := by
        rw [norm_smul (1 / 2 : ℂ)
          (contourCauchySecondVariation data increment increment (extendedContourTangentQuotient data))]
        norm_num only [norm_div, norm_one, Complex.norm_ofNat]
        nlinarith [norm_nonneg (contourCauchySecondVariation data increment increment
          (extendedContourTangentQuotient data))]
      _ ≤ (2 * contourCauchyParameterOperatorConstant outerRadius *
          contourTangentQuotientConstant outerRadius /
          (outerRadius - (innerRadius + outerRadius) / 2)) * ‖increment‖ * ‖increment‖ := by
        apply second_bound.trans
        gcongr
      _ = _ := by field_simp; ring
  have first_bound : ‖contourCauchyDirectionalDerivative data increment
      (contourQuotientDerivativeCLM data increment)‖ ≤
      (contourCauchyParameterOperatorConstant outerRadius *
        contourTangentQuotientLipschitzConstant outerRadius) * ‖increment‖ ^ 2 := by
    apply (contourCauchyDirectionalDerivative_norm_bound data increment
      (contourQuotientDerivativeCLM data increment) outer_near small).trans
    calc
      _ ≤ (contourCauchyParameterOperatorConstant outerRadius *
          (contourTangentQuotientLipschitzConstant outerRadius * ‖increment‖)) * ‖increment‖ := by gcongr
      _ = _ := by ring
  have zero_bound : ‖extendedContourCauchy data (contourQuotientQuadratic data increment)‖ ≤
      (contourCauchyUniformOperatorConstant outerRadius * contourQuotientQuadraticBound outerRadius) *
        ‖increment‖ ^ 2 := by
    exact (extendedContourCauchy_uniform_norm_bound data _ outer_nonnegative small outer_near_le).trans
      ((mul_le_mul_of_nonneg_left quotient_quadratic_bound uniform_nonnegative).trans_eq (by ring))
  have scalar_bound : ‖((Real.pi : ℂ) * Complex.I) • contourQuotientQuadratic data increment‖ ≤
      (Real.pi * contourQuotientQuadraticBound outerRadius) * ‖increment‖ ^ 2 := by
    rw [norm_smul ((Real.pi : ℂ) * Complex.I) (contourQuotientQuadratic data increment)]
    have scalar_norm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [scalar_norm]
    exact (mul_le_mul_of_nonneg_left quotient_quadratic_bound Real.pi_pos.le).trans_eq (by ring)
  unfold contourTangentInnerQuadratic
  have combined := norm_add_le_of_le
    (norm_add_le_of_le (norm_add_le_of_le half_bound first_bound) zero_bound) scalar_bound
  exact combined.trans_eq (by unfold contourTangentInnerQuadraticBound; ring)

end

end EulerNonuniqueness.Paper
