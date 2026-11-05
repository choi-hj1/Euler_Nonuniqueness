import EulerNonuniqueness.Section6.DiagonalFrequencyDifference

noncomputable section

namespace EulerNonuniqueness.Section6

theorem dilation_frequency_product_difference_le (frequency first second positive negative : ℝ)
    (firstLower : (1 / 2 : ℝ) ≤ first) (secondLower : (1 / 2 : ℝ) ≤ second) :
    |(frequency / first - frequency) * positive - (frequency / second - frequency) * negative| ≤
      2 * |frequency| * |first - 1| * |positive - negative| +
        4 * |frequency| * |first - second| * |negative| := by
  have identity : (frequency / first - frequency) * positive - (frequency / second - frequency) * negative =
      (frequency / first - frequency) * (positive - negative) +
        (frequency / first - frequency / second) * negative := by ring
  rw [identity]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (dilation_frequency_deviation_le frequency first firstLower) (abs_nonneg _))
    (mul_le_mul_of_nonneg_right (dilation_frequency_difference_le frequency first second firstLower secondLower) (abs_nonneg _))

def dilationFrequencySaddleError (frequency first second : ℝ) (positive negative : ℝ × ℝ) : ℝ × ℝ :=
  (2 * Real.sqrt 2 * ((frequency / first - frequency) * positive.1 - (frequency / second - frequency) * negative.1),
    -(2 * Real.sqrt 2) * ((frequency / first - frequency) * positive.2 - (frequency / second - frequency) * negative.2))

theorem dilationFrequencySaddleError_norm_le (frequency first second : ℝ) (positive negative : ℝ × ℝ)
    (firstLower : (1 / 2 : ℝ) ≤ first) (secondLower : (1 / 2 : ℝ) ≤ second) :
    ‖dilationFrequencySaddleError frequency first second positive negative‖ ≤
      2 * Real.sqrt 2 *
        (2 * |frequency| * |first - 1| * (|positive.1 - negative.1| + |positive.2 - negative.2|) +
          4 * |frequency| * |first - second| * (|negative.1| + |negative.2|)) := by
  let firstError := (frequency / first - frequency) * positive.1 - (frequency / second - frequency) * negative.1
  let secondError := (frequency / first - frequency) * positive.2 - (frequency / second - frequency) * negative.2
  have identity : dilationFrequencySaddleError frequency first second positive negative =
      (2 * Real.sqrt 2) • (firstError, -secondError) := by
    ext <;> simp only [dilationFrequencySaddleError, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
      firstError, secondError] <;> ring
  rw [identity, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have pairBound : ‖(firstError, -secondError)‖ ≤ |firstError| + |secondError| := by
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_neg]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  apply pairBound.trans
  have firstBound := dilation_frequency_product_difference_le frequency first second positive.1 negative.1 firstLower secondLower
  have secondBound := dilation_frequency_product_difference_le frequency first second positive.2 negative.2 firstLower secondLower
  dsimp only [firstError, secondError]
  convert add_le_add firstBound secondBound using 1 <;> ring

theorem dilation_relative_saddle_remainder_norm_le
    (frequency first second : ℝ) (positive negative firstError secondError : ℝ × ℝ)
    {constant referenceConstant : ℝ} (constantNonnegative : 0 ≤ constant)
    (referenceNonnegative : 0 ≤ referenceConstant)
    (firstLower : (1 / 2 : ℝ) ≤ first) (secondLower : (1 / 2 : ℝ) ≤ second)
    (differenceBound : ‖firstError - secondError‖ ≤ constant *
      (|positive.1 - negative.1| + |positive.2 - negative.2|) *
        (|positive.2 - negative.2| + |negative.1| + |negative.2|))
    (referenceBound : ‖secondError‖ ≤ referenceConstant * (|negative.1| + |negative.2|)) :
    ‖dilationFrequencySaddleError frequency first second positive negative +
      (frequency / first) • (firstError - secondError) + (frequency / first - frequency / second) • secondError‖ ≤
      2 * Real.sqrt 2 *
        (2 * |frequency| * |first - 1| * (|positive.1 - negative.1| + |positive.2 - negative.2|) +
          4 * |frequency| * |first - second| * (|negative.1| + |negative.2|)) +
      2 * |frequency| * (constant * (|positive.1 - negative.1| + |positive.2 - negative.2|) *
        (|positive.2 - negative.2| + |negative.1| + |negative.2|)) +
      (4 * |frequency| * |first - second|) * (referenceConstant * (|negative.1| + |negative.2|)) := by
  have firstPositive : 0 < first := by linarith
  have frequencyBound : |frequency / first| ≤ 2 * |frequency| := by
    rw [abs_div, abs_of_pos firstPositive]
    apply (div_le_iff₀ firstPositive).mpr
    nlinarith [mul_nonneg (abs_nonneg frequency) (sub_nonneg.mpr firstLower)]
  have firstBound : ‖(frequency / first) • (firstError - secondError)‖ ≤
      2 * |frequency| * (constant * (|positive.1 - negative.1| + |positive.2 - negative.2|) *
        (|positive.2 - negative.2| + |negative.1| + |negative.2|)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right frequencyBound (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left differenceBound (by positivity))
  have secondBound : ‖(frequency / first - frequency / second) • secondError‖ ≤
      (4 * |frequency| * |first - second|) * (referenceConstant * (|negative.1| + |negative.2|)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right
      (dilation_frequency_difference_le frequency first second firstLower secondLower) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left referenceBound (by positivity))
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add
      (dilationFrequencySaddleError_norm_le frequency first second positive negative firstLower secondLower) firstBound)) secondBound)

end EulerNonuniqueness.Section6
