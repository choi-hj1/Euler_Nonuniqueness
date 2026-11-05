import EulerNonuniqueness.Section4.InitialRhombusSeparation
import EulerNonuniqueness.Section6.PaperShapeTubeBranch

noncomputable section

namespace EulerNonuniqueness.Paper

theorem initialDiagonals_ratio (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    initialNegativeDiagonal scales index phase unstable / initialPositiveDiagonal scales index phase unstable =
      (Real.sqrt (rhombusRatio * (1 + unstable)) : ℂ) *
        Complex.exp (Complex.I * (Real.pi / 2 + unstable / Real.sqrt 2 : ℝ)) := by
  have ratioPositive : 0 < rhombusRatio * (1 + unstable) :=
    mul_pos reference_rhombusRatio_bounds.1 (by linarith [(abs_le.mp small).1])
  have ratioSmall : rhombusRatio * (1 + unstable) < 1 := by
    nlinarith [reference_rhombusRatio_bounds.1, reference_rhombusRatio_bounds.2, (abs_le.mp small).1, (abs_le.mp small).2]
  have denominatorNonzero : Real.sqrt (1 - rhombusRatio * (1 + unstable)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have exponential : Complex.exp (Complex.I * (phase + Real.pi / 2 + unstable / Real.sqrt 2 : ℝ)) =
      Complex.exp (Complex.I * (phase : ℂ)) *
        Complex.exp (Complex.I * (Real.pi / 2 + unstable / Real.sqrt 2 : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [initialNegativeDiagonal, initialPositiveDiagonal, exponential]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr (scales.length_pos index).ne',
    Complex.ofReal_ne_zero.mpr denominatorNonzero, Complex.exp_ne_zero]
  <;> ring

theorem initialDiagonals_upper_and_shape (scales : Scales) (index : ℕ) (phase unstable : ℝ)
    (small : |unstable| ≤ 1 / 2) :
    0 < (initialNegativeDiagonal scales index phase unstable / initialPositiveDiagonal scales index phase unstable).im ∧
      Section6.pointShapeChart (initialPositiveDiagonal scales index phase unstable)
        (initialNegativeDiagonal scales index phase unstable) = (unstable, 0) := by
  let ratio := rhombusRatio * (1 + unstable)
  let angle := Real.pi / 2 + unstable / Real.sqrt 2
  let quotient := initialNegativeDiagonal scales index phase unstable / initialPositiveDiagonal scales index phase unstable
  have ratioPositive : 0 < ratio :=
    mul_pos reference_rhombusRatio_bounds.1 (by linarith [(abs_le.mp small).1])
  have rootPositive : 0 < Real.sqrt ratio := Real.sqrt_pos.mpr ratioPositive
  have sqrtPositive : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have sqrtLower : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have displacementBound : |unstable / Real.sqrt 2| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos sqrtPositive]
    exact (div_le_iff₀ sqrtPositive).mpr (by nlinarith)
  have anglePositive : 0 < angle := by
    dsimp only [angle]
    linarith [(abs_le.mp displacementBound).1, Real.pi_gt_three]
  have angleBelowPi : angle < Real.pi := by
    dsimp only [angle]
    linarith [(abs_le.mp displacementBound).2, Real.pi_gt_three]
  have quotientIdentity : quotient = (Real.sqrt ratio : ℂ) * Complex.exp (Complex.I * (angle : ℂ)) :=
    initialDiagonals_ratio scales index phase unstable small
  have exponential : Complex.exp (Complex.I * (angle : ℂ)) =
      (Real.cos angle : ℂ) + (Real.sin angle : ℂ) * Complex.I := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have quotientUpper : 0 < quotient.im := by
    rw [quotientIdentity, exponential]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im, Complex.mul_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, zero_add, mul_one]
    exact mul_pos rootPositive (Real.sin_pos_of_pos_of_lt_pi anglePositive angleBelowPi)
  refine ⟨quotientUpper, ?_⟩
  have quotientArgument : Complex.arg quotient = angle := by
    rw [quotientIdentity, exponential]
    simpa only [Complex.ofReal_cos, Complex.ofReal_sin] using
      Complex.arg_mul_cos_add_sin_mul_I rootPositive ⟨by linarith [Real.pi_pos], angleBelowPi.le⟩
  have quotientNorm : ‖quotient‖ ^ 2 = ratio := by
    rw [quotientIdentity, norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos rootPositive]
    exact Real.sq_sqrt ratioPositive.le
  have radialIdentity : Section6.pointShapeRatio (initialPositiveDiagonal scales index phase unstable)
      (initialNegativeDiagonal scales index phase unstable) = ratio := by
    change ‖initialNegativeDiagonal scales index phase unstable‖ ^ 2 /
      ‖initialPositiveDiagonal scales index phase unstable‖ ^ 2 = ratio
    simpa only [quotient, norm_div, div_pow] using quotientNorm
  rw [Section6.pointShapeChart, radialIdentity, Section6.pointShapeAngle_eq_twice_arg_of_upper quotientUpper, quotientArgument]
  dsimp only [Section6.shapeChart, ratio, angle]
  have ratioNonzero : rhombusRatio ≠ 0 := reference_rhombusRatio_bounds.1.ne'
  change (((rhombusRatio * (1 + unstable) / rhombusRatio - 1) +
      (2 * (Real.pi / 2 + unstable / Real.sqrt 2) - Real.pi) / Real.sqrt 2) / 2,
    ((rhombusRatio * (1 + unstable) / rhombusRatio - 1) -
      (2 * (Real.pi / 2 + unstable / Real.sqrt 2) - Real.pi) / Real.sqrt 2) / 2) = (unstable, 0)
  apply Prod.ext <;> dsimp only
  all_goals field_simp [ratioNonzero, sqrtPositive.ne']
  all_goals ring_nf
  all_goals simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  all_goals ring

end EulerNonuniqueness.Paper
