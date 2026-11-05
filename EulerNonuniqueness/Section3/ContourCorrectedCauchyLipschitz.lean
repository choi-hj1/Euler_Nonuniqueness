import EulerNonuniqueness.Section3.ContourQuotientLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

def contourVelocityCauchyDensity (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicHolderHalf :=
  contourCauchyOperator data small (contourTangentQuotient data small) +
    holderComplexMul ((Real.pi : ℂ) * Complex.I) (contourTangentQuotient data small)

def contourVelocityCauchyDensityConstant (radius : ℝ) : ℝ :=
  (contourCauchyUniformOperatorConstant radius + Real.pi) * contourTangentQuotientConstant radius

def contourVelocityCauchyDensityLipschitzConstant (radius : ℝ) : ℝ :=
  contourCauchyParameterOperatorConstant radius * contourTangentQuotientConstant radius +
    (contourCauchyUniformOperatorConstant radius + Real.pi) * contourTangentQuotientLipschitzConstant radius

theorem contourTangentQuotientConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourTangentQuotientConstant radius := by
  have inverse_nonneg := contourTangentInverseConstant_nonneg radius_nonneg radius_small
  unfold contourTangentQuotientConstant
  positivity

theorem contourTangentQuotientLipschitzConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourTangentQuotientLipschitzConstant radius := by
  have inverse_nonneg := contourTangentInverseConstant_nonneg radius_nonneg radius_small
  unfold contourTangentQuotientLipschitzConstant
  positivity

theorem pi_I_norm : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]

theorem contourVelocityCauchyDensity_uniform_norm_bound (data : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityCauchyDensity data (nearby.trans_lt radius_small)‖ ≤ contourVelocityCauchyDensityConstant radius := by
  have operator_nonneg := contourCauchyUniformOperatorConstant_nonneg radius_nonneg radius_small
  have quotient_nonneg := contourTangentQuotientConstant_nonneg radius_nonneg radius_small
  have quotient_bound := contourTangentQuotient_uniform_norm_bound data radius_nonneg radius_small nearby
  have operator_bound := contourCauchyOperatorCLM_uniform_norm_bound data radius_nonneg radius_small nearby
  have evaluation := (contourCauchyOperatorCLM data (nearby.trans_lt radius_small)).le_opNorm
    (contourTangentQuotient data (nearby.trans_lt radius_small))
  have scalar_bound := holderComplexMul_norm_bound ((Real.pi : ℂ) * Complex.I)
    (contourTangentQuotient data (nearby.trans_lt radius_small))
  rw [pi_I_norm] at scalar_bound
  unfold contourVelocityCauchyDensity
  apply (norm_add_le _ _).trans
  calc
    _ ≤ contourCauchyUniformOperatorConstant radius * contourTangentQuotientConstant radius +
        Real.pi * contourTangentQuotientConstant radius :=
      add_le_add (evaluation.trans (mul_le_mul operator_bound quotient_bound (norm_nonneg _) operator_nonneg))
        (scalar_bound.trans (mul_le_mul_of_nonneg_left quotient_bound Real.pi_pos.le))
    _ = _ := by unfold contourVelocityCauchyDensityConstant; ring

theorem holder_operator_evaluation_difference_norm_bound
    (first second : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) (left right : PeriodicHolderHalf) :
    ‖first left - second right‖ ≤ ‖first - second‖ * ‖left‖ + ‖second‖ * ‖left - right‖ := by
  have identity : first left - second right = (first - second) left + second (left - right) := by
    rw [ContinuousLinearMap.sub_apply, map_sub]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans (add_le_add ((first - second).le_opNorm left) (second.le_opNorm (left - right)))

set_option maxHeartbeats 1000000 in
theorem contourVelocityCauchyDensity_parameter_norm_bound (first second : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius) (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityCauchyDensity first (first_near.trans_lt radius_small) -
      contourVelocityCauchyDensity second (second_near.trans_lt radius_small)‖ ≤
      contourVelocityCauchyDensityLipschitzConstant radius * ‖first - second‖ := by
  have operator_nonneg := contourCauchyUniformOperatorConstant_nonneg radius_nonneg radius_small
  have parameter_nonneg := contourCauchyParameterOperatorConstant_nonneg radius_nonneg radius_small
  have quotient_nonneg := contourTangentQuotientConstant_nonneg radius_nonneg radius_small
  have quotient_lipschitz_nonneg := contourTangentQuotientLipschitzConstant_nonneg radius_nonneg radius_small
  have evaluation := holder_operator_evaluation_difference_norm_bound
    (contourCauchyOperatorCLM first (first_near.trans_lt radius_small))
    (contourCauchyOperatorCLM second (second_near.trans_lt radius_small))
    (contourTangentQuotient first (first_near.trans_lt radius_small))
    (contourTangentQuotient second (second_near.trans_lt radius_small))
  have evaluation_bound :
      ‖contourCauchyOperator first (first_near.trans_lt radius_small) (contourTangentQuotient first (first_near.trans_lt radius_small)) -
        contourCauchyOperator second (second_near.trans_lt radius_small) (contourTangentQuotient second (second_near.trans_lt radius_small))‖ ≤
      (contourCauchyParameterOperatorConstant radius * ‖first - second‖) * contourTangentQuotientConstant radius +
        contourCauchyUniformOperatorConstant radius * (contourTangentQuotientLipschitzConstant radius * ‖first - second‖) := by
    apply evaluation.trans
    gcongr
    · exact contourCauchyOperatorCLM_parameter_norm_bound first second radius_nonneg radius_small first_near second_near
    · exact contourTangentQuotient_uniform_norm_bound first radius_nonneg radius_small first_near
    · exact contourCauchyOperatorCLM_uniform_norm_bound second radius_nonneg radius_small second_near
    · exact contourTangentQuotient_parameter_norm_bound first second radius_nonneg radius_small first_near second_near
  have scalar_bound := holderComplexMul_difference_norm_bound ((Real.pi : ℂ) * Complex.I)
    (contourTangentQuotient first (first_near.trans_lt radius_small))
    (contourTangentQuotient second (second_near.trans_lt radius_small))
  rw [pi_I_norm] at scalar_bound
  have scalar_difference_bound := scalar_bound.trans (mul_le_mul_of_nonneg_left
    (contourTangentQuotient_parameter_norm_bound first second radius_nonneg radius_small first_near second_near) Real.pi_pos.le)
  have identity : contourVelocityCauchyDensity first (first_near.trans_lt radius_small) -
      contourVelocityCauchyDensity second (second_near.trans_lt radius_small) =
      (contourCauchyOperator first (first_near.trans_lt radius_small) (contourTangentQuotient first (first_near.trans_lt radius_small)) -
        contourCauchyOperator second (second_near.trans_lt radius_small) (contourTangentQuotient second (second_near.trans_lt radius_small))) +
      (holderComplexMul ((Real.pi : ℂ) * Complex.I) (contourTangentQuotient first (first_near.trans_lt radius_small)) -
        holderComplexMul ((Real.pi : ℂ) * Complex.I) (contourTangentQuotient second (second_near.trans_lt radius_small))) := by
    unfold contourVelocityCauchyDensity
    abel
  rw [identity]
  apply (norm_add_le _ _).trans ((add_le_add evaluation_bound scalar_difference_bound).trans_eq ?_)
  unfold contourVelocityCauchyDensityLipschitzConstant
  ring

end

end EulerNonuniqueness.Paper
