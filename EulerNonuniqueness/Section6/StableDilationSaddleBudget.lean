import EulerNonuniqueness.Section6.DilationFrequencySaddleError

noncomputable section

namespace EulerNonuniqueness.Section6

theorem stable_dilation_saddle_remainder_le
    (frequency firstDilation secondDilation : ℝ)
    (firstChart secondChart firstError secondError : ℝ × ℝ)
    {referenceSize pairConstant referenceConstant : ℝ}
    (referenceSizeNonnegative : 0 ≤ referenceSize)
    (pairNonnegative : 0 ≤ pairConstant) (referenceNonnegative : 0 ≤ referenceConstant)
    (firstLower : (1 / 2 : ℝ) ≤ firstDilation) (secondLower : (1 / 2 : ℝ) ≤ secondDilation)
    (referenceStable : |secondChart.2| ≤ referenceSize)
    (referenceDilation : |secondDilation - 1| ≤ referenceSize)
    (pairBound : |(firstError - secondError).2| ≤ pairConstant *
      (((|firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|) + referenceSize) *
        |firstChart.2 - secondChart.2| + referenceSize *
          (|firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|)))
    (referenceBound : |secondError.2| ≤ referenceConstant * referenceSize) :
    let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
    let stable := |firstChart.2 - secondChart.2|
    let dilation := |firstDilation - secondDilation|
    |(dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart +
        (frequency / firstDilation) • (firstError - secondError) +
        (frequency / firstDilation - frequency / secondDilation) • secondError).2| ≤
      (16 + 2 * pairConstant + 4 * referenceConstant) * |frequency| *
        ((shape + dilation + referenceSize) * stable + referenceSize * (shape + dilation)) := by
  dsimp only
  let shape := |firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|
  let stable := |firstChart.2 - secondChart.2|
  let dilation := |firstDilation - secondDilation|
  let budget := (shape + dilation + referenceSize) * stable + referenceSize * (shape + dilation)
  have shapeNonnegative : 0 ≤ shape := by dsimp only [shape]; positivity
  have stableNonnegative : 0 ≤ stable := abs_nonneg _
  have dilationNonnegative : 0 ≤ dilation := abs_nonneg _
  have firstPositive : 0 < firstDilation := by linarith only [firstLower]
  have deviation : |firstDilation - 1| ≤ dilation + referenceSize := by
    have triangle : |firstDilation - 1| ≤ |firstDilation - secondDilation| + |secondDilation - 1| := by
      have identity : firstDilation - 1 = (firstDilation - secondDilation) + (secondDilation - 1) := by ring
      rw [identity]
      exact abs_add_le _ _
    exact triangle.trans (add_le_add_left referenceDilation _)
  have sqrtBound : 2 * Real.sqrt 2 ≤ (4 : ℝ) := by
    have lower := Real.sqrt_nonneg (2 : ℝ)
    have square := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [lower, square]
  have dilationTerm :
      |(dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart).2| ≤
        |frequency| * (8 * (dilation + referenceSize) * stable + 16 * dilation * referenceSize) := by
    have original := dilation_frequency_product_difference_le frequency firstDilation secondDilation
      firstChart.2 secondChart.2 firstLower secondLower
    have enlarged := original.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left deviation (by positivity : 0 ≤ 2 * |frequency|)) stableNonnegative)
      (mul_le_mul_of_nonneg_left referenceStable (by positivity : 0 ≤ 4 * |frequency| * dilation)))
    change |-(2 * Real.sqrt 2) * _| ≤ _
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.sqrt 2)]
    calc
      _ ≤ (2 * Real.sqrt 2) *
          (2 * |frequency| * (dilation + referenceSize) * stable + 4 * |frequency| * dilation * referenceSize) :=
        mul_le_mul_of_nonneg_left enlarged (by positivity)
      _ ≤ 4 * (2 * |frequency| * (dilation + referenceSize) * stable + 4 * |frequency| * dilation * referenceSize) :=
        mul_le_mul_of_nonneg_right sqrtBound (by positivity)
      _ = _ := by ring
  have frequencyBound : |frequency / firstDilation| ≤ 2 * |frequency| := by
    rw [abs_div, abs_of_pos firstPositive]
    apply (div_le_iff₀ firstPositive).mpr
    nlinarith only [mul_nonneg (abs_nonneg frequency) (sub_nonneg.mpr firstLower)]
  have pairTerm : |((frequency / firstDilation) • (firstError - secondError)).2| ≤
      2 * |frequency| * (pairConstant * ((shape + referenceSize) * stable + referenceSize * shape)) := by
    simp only [Prod.smul_snd, smul_eq_mul, abs_mul]
    exact mul_le_mul frequencyBound pairBound (abs_nonneg _) (by positivity)
  have referenceTerm : |((frequency / firstDilation - frequency / secondDilation) • secondError).2| ≤
      (4 * |frequency| * dilation) * (referenceConstant * referenceSize) := by
    simp only [Prod.smul_snd, smul_eq_mul, abs_mul]
    exact mul_le_mul (dilation_frequency_difference_le frequency firstDilation secondDilation firstLower secondLower)
      referenceBound (abs_nonneg _) (by positivity)
  have dilationBudget : 8 * (dilation + referenceSize) * stable + 16 * dilation * referenceSize ≤ 16 * budget := by
    dsimp only [budget]
    nlinarith only [mul_nonneg shapeNonnegative stableNonnegative,
      mul_nonneg dilationNonnegative stableNonnegative, mul_nonneg referenceSizeNonnegative stableNonnegative,
      mul_nonneg referenceSizeNonnegative shapeNonnegative]
  have pairBudget : (shape + referenceSize) * stable + referenceSize * shape ≤ budget := by
    dsimp only [budget]
    nlinarith only [mul_nonneg dilationNonnegative stableNonnegative,
      mul_nonneg referenceSizeNonnegative dilationNonnegative]
  have referenceBudget : dilation * referenceSize ≤ budget := by
    dsimp only [budget]
    nlinarith only [mul_nonneg (add_nonneg (add_nonneg shapeNonnegative dilationNonnegative) referenceSizeNonnegative)
      stableNonnegative, mul_nonneg referenceSizeNonnegative shapeNonnegative]
  calc
    _ ≤ |(dilationFrequencySaddleError frequency firstDilation secondDilation firstChart secondChart).2| +
        |((frequency / firstDilation) • (firstError - secondError)).2| +
        |((frequency / firstDilation - frequency / secondDilation) • secondError).2| :=
      (abs_add_le _ _).trans (add_le_add_right (abs_add_le _ _) _)
    _ ≤ |frequency| * (8 * (dilation + referenceSize) * stable + 16 * dilation * referenceSize) +
        2 * |frequency| * (pairConstant * ((shape + referenceSize) * stable + referenceSize * shape)) +
        (4 * |frequency| * dilation) * (referenceConstant * referenceSize) :=
      add_le_add (add_le_add dilationTerm pairTerm) referenceTerm
    _ = |frequency| * (8 * (dilation + referenceSize) * stable + 16 * dilation * referenceSize) +
        (2 * pairConstant * |frequency|) * ((shape + referenceSize) * stable + referenceSize * shape) +
        (4 * referenceConstant * |frequency|) * (dilation * referenceSize) := by ring
    _ ≤ |frequency| * (16 * budget) + (2 * pairConstant * |frequency|) * budget +
        (4 * referenceConstant * |frequency|) * budget :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left dilationBudget (abs_nonneg frequency))
        (mul_le_mul_of_nonneg_left pairBudget (by positivity)))
        (mul_le_mul_of_nonneg_left referenceBudget (by positivity))
    _ = _ := by dsimp only [budget, shape, stable, dilation]; ring

end EulerNonuniqueness.Section6

