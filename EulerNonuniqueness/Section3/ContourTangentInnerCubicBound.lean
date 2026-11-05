import EulerNonuniqueness.Section3.ContourTangentInnerQuadraticBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourTangentInnerCubicBound (innerRadius outerRadius : ℝ) : ℝ :=
  16 * contourCauchyUniformOperatorConstant outerRadius * contourTangentQuotientConstant outerRadius /
      (outerRadius - innerRadius) ^ 3 +
    8 * contourCauchyUniformOperatorConstant outerRadius * contourTangentQuotientLipschitzConstant outerRadius /
      (outerRadius - innerRadius) ^ 2 +
    contourCauchyParameterOperatorConstant outerRadius * contourQuotientQuadraticBound outerRadius +
    (contourCauchyUniformOperatorConstant outerRadius + Real.pi) * contourQuotientCubicBound outerRadius

theorem contourTangentInner_cubic_uniform_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (increment_small : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverse_small : ‖increment‖ ≤ (1 - outerRadius) / 2) (increment_bound : ‖increment‖ ≤ 1) :
    ‖contourTangentInner (data + increment) - contourTangentInner data -
      contourTangentInnerLinear data increment - contourTangentInnerQuadratic data increment‖ ≤
      contourTangentInnerCubicBound innerRadius outerRadius * ‖increment‖ ^ 3 := by
  have outer_nonnegative := nonnegative.trans gap.le
  have outer_near := nearby.trans_lt gap
  have outer_near_le := outer_near.le
  have gap_positive : 0 < outerRadius - innerRadius := sub_pos.mpr gap
  have data_gap_positive : 0 < outerRadius - ‖data - standardCircleBanach‖ := sub_pos.mpr outer_near
  have gap_lower : outerRadius - innerRadius ≤ outerRadius - ‖data - standardCircleBanach‖ := by linarith
  have uniform_nonnegative := contourCauchyUniformOperatorConstant_nonneg outer_nonnegative small
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg outer_nonnegative small
  have inverse_nonnegative := contourTangentInverseConstant_nonneg outer_nonnegative small
  have quotient_nonnegative : 0 ≤ contourTangentQuotientConstant outerRadius := by
    unfold contourTangentQuotientConstant
    positivity
  have linear_nonnegative : 0 ≤ contourTangentQuotientLipschitzConstant outerRadius := by
    unfold contourTangentQuotientLipschitzConstant
    positivity
  have quotient_bound := extendedContourTangentQuotient_uniform_norm_bound data outer_nonnegative small outer_near_le
  have quotient_linear_bound := contourQuotientDerivative_uniform_norm_bound data increment
    outer_nonnegative small outer_near_le
  have quotient_quadratic_bound : ‖contourQuotientQuadratic data increment‖ ≤
      contourQuotientQuadraticBound outerRadius * ‖increment‖ ^ 2 :=
    contourQuotientQuadratic_norm_bound data increment outer_nonnegative small outer_near_le
  have next_nearby : ‖data + increment - standardCircleBanach‖ ≤ outerRadius := by
    have identity : data + increment - standardCircleBanach =
        (data - standardCircleBanach) + increment := by abel
    rw [identity]
    exact (norm_add_le (data - standardCircleBanach) increment).trans (by linarith)
  have quotient_remainder :
      ‖extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
        contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment‖ ≤
      contourQuotientCubicBound outerRadius * ‖increment‖ ^ 3 :=
    contourQuotient_cubic_remainder_norm data increment outer_nonnegative small
      outer_near_le next_nearby inverse_small increment_bound
  have term_zero :
      (16 * (contourCauchyUniformOperatorConstant outerRadius * ‖extendedContourTangentQuotient data‖) /
        (outerRadius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 ≤
      (16 * contourCauchyUniformOperatorConstant outerRadius * contourTangentQuotientConstant outerRadius /
        (outerRadius - innerRadius) ^ 3) * ‖increment‖ ^ 3 := by
    calc
      _ ≤ (16 * (contourCauchyUniformOperatorConstant outerRadius *
            contourTangentQuotientConstant outerRadius) /
          (outerRadius - innerRadius) ^ 3) * ‖increment‖ ^ 3 := by gcongr
      _ = _ := by ring
  have term_linear :
      (8 * (contourCauchyUniformOperatorConstant outerRadius * ‖contourQuotientDerivativeCLM data increment‖) /
        (outerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 ≤
      (8 * contourCauchyUniformOperatorConstant outerRadius * contourTangentQuotientLipschitzConstant outerRadius /
        (outerRadius - innerRadius) ^ 2) * ‖increment‖ ^ 3 := by
    calc
      _ ≤ (8 * (contourCauchyUniformOperatorConstant outerRadius *
            (contourTangentQuotientLipschitzConstant outerRadius * ‖increment‖)) /
          (outerRadius - innerRadius) ^ 2) * ‖increment‖ ^ 2 := by gcongr
      _ = _ := by ring
  have term_quadratic : contourCauchyParameterOperatorConstant outerRadius * ‖increment‖ *
      ‖contourQuotientQuadratic data increment‖ ≤
      (contourCauchyParameterOperatorConstant outerRadius * contourQuotientQuadraticBound outerRadius) *
        ‖increment‖ ^ 3 := by
    calc
      _ ≤ contourCauchyParameterOperatorConstant outerRadius * ‖increment‖ *
          (contourQuotientQuadraticBound outerRadius * ‖increment‖ ^ 2) := by gcongr
      _ = _ := by ring
  have term_remainder : (contourCauchyUniformOperatorConstant outerRadius + Real.pi) *
      ‖extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
        contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment‖ ≤
      ((contourCauchyUniformOperatorConstant outerRadius + Real.pi) * contourQuotientCubicBound outerRadius) *
        ‖increment‖ ^ 3 :=
    (mul_le_mul_of_nonneg_left quotient_remainder (by positivity)).trans_eq (by ring)
  have actual := contourTangentInner_remainder_bound data increment outer_near small
    (increment_small.trans (by linarith))
  exact actual.trans
    ((add_le_add (add_le_add (add_le_add term_zero term_linear) term_quadratic) term_remainder).trans_eq
      (by unfold contourTangentInnerCubicBound; ring))

end

end EulerNonuniqueness.Paper
