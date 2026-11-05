import EulerNonuniqueness.General.LogPerturbation

noncomputable section

namespace EulerNonuniqueness

theorem perturbed_log_cos_bound {angle coefficient coefficientError : ℝ}
    (angleSmall : |angle| ≤ 1 / 2) (_errorNonnegative : 0 ≤ coefficientError)
    (errorSmall : coefficientError ≤ 1 / 8)
    (coefficientClose : |coefficient - Real.cos angle| ≤ coefficientError) :
    3 / 4 ≤ coefficient ∧ |Real.log coefficient| ≤ angle ^ 2 + 2 * coefficientError := by
  have angleSquare : angle ^ 2 ≤ 1 / 4 := by
    nlinarith only [pow_le_pow_left₀ (abs_nonneg angle) angleSmall 2, sq_abs angle]
  have cosineLower : 1 - angle ^ 2 / 2 ≤ Real.cos angle := Real.one_sub_sq_div_two_le_cos
  have lower : 3 / 4 ≤ coefficient := by
    linarith only [(abs_le.mp coefficientClose).1, cosineLower, angleSquare, errorSmall]
  have closeToOne : |coefficient - 1| ≤ angle ^ 2 / 2 + coefficientError := by
    apply abs_le.mpr
    constructor
    · linarith only [(abs_le.mp coefficientClose).1, cosineLower]
    · linarith only [(abs_le.mp coefficientClose).2, Real.cos_le_one angle, sq_nonneg angle]
  have logarithmic := abs_log_sub_log_le_of_relative_error (first := 1) (second := coefficient)
    (error := angle ^ 2 / 2 + coefficientError) zero_lt_one closeToOne
    (by linarith only [angleSquare, errorSmall])
  have simplified : |Real.log coefficient| ≤ 2 * (angle ^ 2 / 2 + coefficientError) := by
    simpa only [Real.log_one, sub_zero, div_one] using logarithmic
  exact ⟨lower, simplified.trans_eq (by ring)⟩

theorem perturbed_log_cos_timing_recurrence
    {ratio current next coefficient coefficientError timingError : ℝ}
    (ratioLarge : 4 ≤ ratio) (coefficientErrorNonnegative : 0 ≤ coefficientError)
    (coefficientErrorSmall : coefficientError ≤ 1 / 8) (_timingErrorNonnegative : 0 ≤ timingError)
    (angleSmall : |2 * (1 + ratio⁻¹) * next| ≤ 1 / 2)
    (coefficientClose : |coefficient - Real.cos (2 * (1 + ratio⁻¹) * next)| ≤ coefficientError)
    (delayClose : |current - ratio⁻¹ * next + Real.log coefficient / (2 * Real.sqrt 2)| ≤ timingError) :
    |current| ≤ ratio⁻¹ * |next| + 4 * next ^ 2 + coefficientError + timingError := by
  have ratioPositive : 0 < ratio := by linarith only [ratioLarge]
  have inverseNonnegative : 0 ≤ ratio⁻¹ := inv_nonneg.mpr ratioPositive.le
  have inverseBound : ratio⁻¹ ≤ 1 / 4 := by
    rw [← one_div]
    apply (div_le_iff₀ ratioPositive).mpr
    linarith only [ratioLarge]
  have sqrtOne : 1 ≤ Real.sqrt 2 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  have denominatorPositive : 0 < 2 * Real.sqrt 2 := by positivity
  have logarithmic := (perturbed_log_cos_bound angleSmall coefficientErrorNonnegative
    coefficientErrorSmall coefficientClose).2
  have factorSquare : (1 + ratio⁻¹) ^ 2 ≤ (5 / 4 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith only [inverseBound]) 2
  have angleSquare : (2 * (1 + ratio⁻¹) * next) ^ 2 / 2 ≤ 4 * next ^ 2 := by
    nlinarith only [mul_le_mul_of_nonneg_right factorSquare (sq_nonneg next), sq_nonneg next]
  have logarithmicCost : |Real.log coefficient| / (2 * Real.sqrt 2) ≤ 4 * next ^ 2 + coefficientError := by
    calc
      _ ≤ ((2 * (1 + ratio⁻¹) * next) ^ 2 + 2 * coefficientError) / (2 * Real.sqrt 2) :=
        div_le_div_of_nonneg_right logarithmic denominatorPositive.le
      _ ≤ ((2 * (1 + ratio⁻¹) * next) ^ 2 + 2 * coefficientError) / 2 :=
        div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith only [sqrtOne])
      _ = (2 * (1 + ratio⁻¹) * next) ^ 2 / 2 + coefficientError := by ring
      _ ≤ _ := add_le_add_right angleSquare coefficientError
  have triangle : |current| ≤ timingError + ratio⁻¹ * |next| + |Real.log coefficient| / (2 * Real.sqrt 2) := by
    calc
      _ = |(current - ratio⁻¹ * next + Real.log coefficient / (2 * Real.sqrt 2)) +
          ratio⁻¹ * next - Real.log coefficient / (2 * Real.sqrt 2)| := by congr 1; ring
      _ ≤ |current - ratio⁻¹ * next + Real.log coefficient / (2 * Real.sqrt 2)| +
          |ratio⁻¹ * next| + |Real.log coefficient / (2 * Real.sqrt 2)| :=
        (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ timingError + ratio⁻¹ * |next| + |Real.log coefficient| / (2 * Real.sqrt 2) := by
        rw [abs_mul, abs_of_nonneg inverseNonnegative, abs_div, abs_of_pos denominatorPositive]
        exact add_le_add_right (add_le_add_right delayClose _) _
  linarith only [triangle, logarithmicCost]

end EulerNonuniqueness
