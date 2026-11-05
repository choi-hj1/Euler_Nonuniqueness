import EulerNonuniqueness.Section3.ContourCorrectedCauchyLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem contourVelocityCauchyDensityConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourVelocityCauchyDensityConstant radius := by
  have operator_nonneg := contourCauchyUniformOperatorConstant_nonneg radius_nonneg radius_small
  have quotient_nonneg := contourTangentQuotientConstant_nonneg radius_nonneg radius_small
  unfold contourVelocityCauchyDensityConstant
  positivity

theorem contourVelocityCauchyDensityLipschitzConstant_nonneg {radius : ℝ} (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourVelocityCauchyDensityLipschitzConstant radius := by
  have operator_nonneg := contourCauchyUniformOperatorConstant_nonneg radius_nonneg radius_small
  have parameter_nonneg := contourCauchyParameterOperatorConstant_nonneg radius_nonneg radius_small
  have quotient_nonneg := contourTangentQuotientConstant_nonneg radius_nonneg radius_small
  have quotient_lipschitz_nonneg := contourTangentQuotientLipschitzConstant_nonneg radius_nonneg radius_small
  unfold contourVelocityCauchyDensityLipschitzConstant
  positivity

def contourVelocityDerivativeConstant (radius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * (2 * (radius + 2) * contourVelocityCauchyDensityConstant radius)

def contourVelocityDerivativeLipschitzConstant (radius : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * (2 * contourVelocityCauchyDensityConstant radius +
    2 * (radius + 2) * contourVelocityCauchyDensityLipschitzConstant radius)

theorem negative_quarter_pi_norm : ‖-((1 / (4 * Real.pi) : ℝ) : ℂ)‖ = 1 / (4 * Real.pi) := by
  rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / (4 * Real.pi))]

theorem contourVelocityDerivativeHolder_uniform_norm_bound (data : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityDerivativeHolder data (nearby.trans_lt radius_small)‖ ≤ contourVelocityDerivativeConstant radius := by
  have density_nonneg := contourVelocityCauchyDensityConstant_nonneg radius_nonneg radius_small
  change ‖holderComplexMul (-((1 / (4 * Real.pi) : ℝ) : ℂ))
    (holderProduct (holderConjugate data.val.2) (holderConjugate (contourVelocityCauchyDensity data (nearby.trans_lt radius_small))))‖ ≤ _
  have bound := holderComplexMul_norm_bound (-((1 / (4 * Real.pi) : ℝ) : ℂ))
    (holderProduct (holderConjugate data.val.2) (holderConjugate (contourVelocityCauchyDensity data (nearby.trans_lt radius_small))))
  rw [negative_quarter_pi_norm] at bound
  apply bound.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 1 / (4 * Real.pi))
  apply (holderProduct_norm_bound _ _).trans
  gcongr
  · exact (holderConjugate_norm_bound data.val.2).trans
      ((PeriodicC1HolderHalf.tangent_norm_bound data).trans (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby))
  · exact (holderConjugate_norm_bound _).trans
      (contourVelocityCauchyDensity_uniform_norm_bound data radius_nonneg radius_small nearby)

set_option maxHeartbeats 1000000 in
theorem contourVelocityDerivativeHolder_parameter_norm_bound (first second : PeriodicC1HolderHalf) {radius : ℝ}
    (radius_nonneg : 0 ≤ radius) (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_near : ‖first - standardCircleBanach‖ ≤ radius) (second_near : ‖second - standardCircleBanach‖ ≤ radius) :
    ‖contourVelocityDerivativeHolder first (first_near.trans_lt radius_small) -
      contourVelocityDerivativeHolder second (second_near.trans_lt radius_small)‖ ≤
      contourVelocityDerivativeLipschitzConstant radius * ‖first - second‖ := by
  have density_nonneg := contourVelocityCauchyDensityConstant_nonneg radius_nonneg radius_small
  have lipschitz_nonneg := contourVelocityCauchyDensityLipschitzConstant_nonneg radius_nonneg radius_small
  change ‖holderComplexMul (-((1 / (4 * Real.pi) : ℝ) : ℂ))
      (holderProduct (holderConjugate first.val.2) (holderConjugate (contourVelocityCauchyDensity first (first_near.trans_lt radius_small)))) -
    holderComplexMul (-((1 / (4 * Real.pi) : ℝ) : ℂ))
      (holderProduct (holderConjugate second.val.2) (holderConjugate (contourVelocityCauchyDensity second (second_near.trans_lt radius_small))))‖ ≤ _
  have outer_bound := holderComplexMul_difference_norm_bound (-((1 / (4 * Real.pi) : ℝ) : ℂ))
    (holderProduct (holderConjugate first.val.2) (holderConjugate (contourVelocityCauchyDensity first (first_near.trans_lt radius_small))))
    (holderProduct (holderConjugate second.val.2) (holderConjugate (contourVelocityCauchyDensity second (second_near.trans_lt radius_small))))
  rw [negative_quarter_pi_norm] at outer_bound
  apply outer_bound.trans
  have product_bound := holderProduct_difference_norm_bound
    (holderConjugate first.val.2) (holderConjugate (contourVelocityCauchyDensity first (first_near.trans_lt radius_small)))
    (holderConjugate second.val.2) (holderConjugate (contourVelocityCauchyDensity second (second_near.trans_lt radius_small)))
  have product_estimate :
      ‖holderProduct (holderConjugate first.val.2) (holderConjugate (contourVelocityCauchyDensity first (first_near.trans_lt radius_small))) -
        holderProduct (holderConjugate second.val.2) (holderConjugate (contourVelocityCauchyDensity second (second_near.trans_lt radius_small)))‖ ≤
      2 * ‖first - second‖ * contourVelocityCauchyDensityConstant radius +
        2 * (radius + 2) * (contourVelocityCauchyDensityLipschitzConstant radius * ‖first - second‖) := by
    apply product_bound.trans
    gcongr
    · exact (holderConjugate_difference_norm_bound first.val.2 second.val.2).trans
        (PeriodicC1HolderHalf.tangent_difference_norm_bound first second)
    · exact (holderConjugate_norm_bound _).trans
        (contourVelocityCauchyDensity_uniform_norm_bound first radius_nonneg radius_small first_near)
    · exact (holderConjugate_norm_bound second.val.2).trans
        ((PeriodicC1HolderHalf.tangent_norm_bound second).trans (PeriodicC1HolderHalf.norm_le_radius_add_two second second_near))
    · exact (holderConjugate_difference_norm_bound _ _).trans
        (contourVelocityCauchyDensity_parameter_norm_bound first second radius_nonneg radius_small first_near second_near)
  apply (mul_le_mul_of_nonneg_left product_estimate (by positivity : 0 ≤ 1 / (4 * Real.pi))).trans_eq
  unfold contourVelocityDerivativeLipschitzConstant
  ring

end

end EulerNonuniqueness.Paper
