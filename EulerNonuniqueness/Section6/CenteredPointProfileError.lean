import EulerNonuniqueness.Section6.CenteredPointNormScaling

noncomputable section

namespace EulerNonuniqueness.Section6

theorem centered_point_profile_error (positions reference : FourPointConfiguration)
    {length : ℝ} {rotation : ℂ} (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1) :
    ‖positions - (fun target => fourPointArithmeticCenter positions + (length : ℂ) * rotation * reference target)‖ =
      length * ‖(fun target => ((length : ℂ) * rotation)⁻¹ * fourPointCenterProjection positions target) - reference‖ := by
  let scale : ℂ := (length : ℂ) * rotation
  have nonzero : scale ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr lengthPositive.ne')
    (norm_ne_zero_iff.mp (by rw [rotationNorm]; norm_num))
  have identity : positions - (fun target => fourPointArithmeticCenter positions + scale * reference target) =
      scale • ((fun target => scale⁻¹ * fourPointCenterProjection positions target) - reference) := by
    funext target
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, fourPointCenterProjection, mul_sub,
      ← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]
    ring
  rw [identity, norm_smul]
  congr 1
  simp only [scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, rotationNorm, mul_one]

end EulerNonuniqueness.Section6
