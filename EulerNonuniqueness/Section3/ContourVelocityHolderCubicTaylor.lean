import EulerNonuniqueness.Section3.ContourVelocityQuadratic

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourVelocityHolder_cubic_taylor_bound
    (data increment : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (radius - ‖data - standardCircleBanach‖) / 4) :
    ‖holderContourVelocity (data + increment) - holderContourVelocity data -
        contourVelocityHolderDerivativeCLM data near small increment -
        contourVelocityHolderQuadratic data increment‖ ≤
      (1 / (4 * Real.pi)) *
        (16 * (contourCauchyUniformOperatorConstant radius *
            ‖holderConjugate (c1ValueHolder data)‖) /
            (radius - ‖data - standardCircleBanach‖) ^ 3 +
          16 * contourCauchyUniformOperatorConstant radius /
            (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 3 := by
  let density := holderConjugate (c1ValueHolder data)
  let densityIncrement := holderConjugate (c1ValueHolder increment)
  let remainder := extendedContourCauchy (data + increment) (density + densityIncrement) -
    extendedContourCauchy data density -
    (contourCauchyDirectionalDerivative data increment density +
      extendedContourCauchy data densityIncrement) -
    ((1 / 2 : ℂ) • contourCauchySecondVariation data increment increment density +
      contourCauchyDirectionalDerivative data increment densityIncrement)
  have bound := contourCauchy_joint_cubic_taylor_bound data increment density densityIncrement
    near small increment_small
  have density_bound : ‖densityIncrement‖ ≤ 2 * ‖increment‖ :=
    (holderConjugate_norm_bound (c1ValueHolder increment)).trans
      (c1ValueHolder_norm_bound increment)
  have uniform_nonnegative := contourCauchyUniformOperatorConstant_nonneg
    ((norm_nonneg _).trans near.le) small
  have mixed_bound : (8 * (contourCauchyUniformOperatorConstant radius * ‖densityIncrement‖) /
      (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 ≤
      (16 * contourCauchyUniformOperatorConstant radius /
        (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 3 := by
    calc
      _ ≤ (8 * (contourCauchyUniformOperatorConstant radius * (2 * ‖increment‖)) /
          (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left density_bound uniform_nonnegative) (by norm_num)
      _ = _ := by ring
  have remainder_bound : ‖remainder‖ ≤
      (16 * (contourCauchyUniformOperatorConstant radius * ‖density‖) /
          (radius - ‖data - standardCircleBanach‖) ^ 3 +
        16 * contourCauchyUniformOperatorConstant radius /
          (radius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 3 :=
    bound.trans ((add_le_add_left mixed_bound _).trans_eq (by ring))
  rw [contourVelocityHolder_quadratic_remainder_identity data increment near small]
  change ‖-(1 / (4 * Real.pi) : ℂ) • holderConjugate remainder‖ ≤ _
  rw [norm_smul (-(1 / (4 * Real.pi) : ℂ)) (holderConjugate remainder), norm_neg]
  have prefactor_norm : ‖(1 / (4 * Real.pi) : ℂ)‖ = 1 / (4 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [prefactor_norm]
  exact (mul_le_mul_of_nonneg_left
    ((holderConjugate_norm_bound remainder).trans remainder_bound) (by positivity)).trans_eq
      (by dsimp only [density]; ring)

end

end EulerNonuniqueness.Paper
