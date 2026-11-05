import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace EulerNonuniqueness.General

theorem reference_decay_saddle_budget
    {frequency reference difference dilation stable constant referenceConstant : ℝ}
    (frequencyNonnegative : 0 ≤ frequency) (referenceNonnegative : 0 ≤ reference)
    (differenceNonnegative : 0 ≤ difference) (dilationNonnegative : 0 ≤ dilation)
    (stableNonnegative : 0 ≤ stable) (stableBound : stable ≤ difference)
    (constantNonnegative : 0 ≤ constant) (referenceConstantNonnegative : 0 ≤ referenceConstant) :
    2 * Real.sqrt 2 * (2 * frequency * (reference + dilation) * difference +
        4 * frequency * dilation * reference) +
      2 * frequency * (constant * difference * (stable + reference)) +
      (4 * frequency * dilation) * (referenceConstant * reference) ≤
      (1 + 12 * Real.sqrt 2 + 4 * constant + 4 * referenceConstant) * frequency *
        ((reference + dilation + difference) * difference + reference * dilation) := by
  have stableTerm := mul_le_mul_of_nonneg_left stableBound
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) frequencyNonnegative)
      (mul_nonneg constantNonnegative differenceNonnegative))
  have first : 0 ≤ frequency * reference * difference := by positivity
  have second : 0 ≤ frequency * dilation * difference := by positivity
  have third : 0 ≤ frequency * difference ^ 2 := by positivity
  have fourth : 0 ≤ frequency * reference * dilation := by positivity
  have sqrtNonnegative : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  nlinarith [mul_nonneg sqrtNonnegative first, mul_nonneg sqrtNonnegative second,
    mul_nonneg sqrtNonnegative third, mul_nonneg sqrtNonnegative fourth,
    mul_nonneg constantNonnegative first, mul_nonneg constantNonnegative second,
    mul_nonneg constantNonnegative third, mul_nonneg constantNonnegative fourth,
    mul_nonneg referenceConstantNonnegative first, mul_nonneg referenceConstantNonnegative second,
    mul_nonneg referenceConstantNonnegative third]

end EulerNonuniqueness.General
