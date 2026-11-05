import EulerNonuniqueness.Section6.NormalizedOddInternalRelative

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem fourPointOddInternalError_global_normalized_relative_bound {lower upper minimumPositive : ℝ}
    (lowerPositive : 0 < lower) (ordered : lower ≤ upper) (upperSmall : upper < 1)
    (minimumPositiveBound : 0 < minimumPositive) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ first second : FourPointConfiguration,
      (fourPointOddPart second).1 = 1 → minimumPositive ≤ ‖(fourPointOddPart first).1‖ →
      lower ≤ ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ →
      ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ ≤ upper →
      lower ≤ ‖(fourPointOddPart second).2‖ → ‖(fourPointOddPart second).2‖ ≤ upper →
      ‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖ < radius →
      ‖fourPointOddInternalError coefficient first - fourPointOddInternalError coefficient second‖ ≤
        bound * |coefficient| *
          ((‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) *
              ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
            ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
              centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ *
                ‖fourPointSignedMoment second‖ ^ 2) / 16 := by
  obtain ⟨relativeBound, relativeNonnegative, relativeRadius, relativePositive, relativeEstimate⟩ :=
    fourPointOddInternalError_normalized_relative_bound lowerPositive ordered upperSmall
  obtain ⟨absoluteBound, absoluteNonnegative, absoluteRadius, absolutePositive, absoluteEstimate⟩ :=
    fourPointOdd_uniform_physical_internal_bound lowerPositive ordered upperSmall
  let minimum := min minimumPositive 1
  have minimumPositive' : 0 < minimum := lt_min minimumPositiveBound (by norm_num)
  let radius := min (absoluteRadius * minimum) (2 * relativeRadius)
  let bound := relativeBound + absoluteBound / minimum ^ 3 * (1 + 4 / relativeRadius)
  have radiusPositive : 0 < radius := lt_min (mul_pos absolutePositive minimumPositive') (by positivity)
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient first second secondPositive firstPositive firstLower firstUpper secondLower secondUpper momentSmall
  let firstMoment := ‖fourPointSignedMoment first‖
  let secondMoment := ‖fourPointSignedMoment second‖
  let differenceMoment := ‖fourPointSignedMoment first - fourPointSignedMoment second‖
  let centralDifference := ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
    centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖
  have firstMinimum : minimum ≤ ‖(fourPointOddPart first).1‖ := (min_le_left _ _).trans firstPositive
  have secondMinimum : minimum ≤ ‖(fourPointOddPart second).1‖ := by
    rw [secondPositive, norm_one]
    exact min_le_right _ _
  have firstNonzero : (fourPointOddPart first).1 ≠ 0 := norm_pos_iff.mp (minimumPositive'.trans_le firstMinimum)
  have secondNonzero : (fourPointOddPart second).1 ≠ 0 := by rw [secondPositive]; exact one_ne_zero
  have firstCollision : FourPointNoncollision (centrallySymmetricFourPoint
      (fourPointOddPart first).1 (fourPointOddPart first).2) := by
    apply centrallySymmetricFourPoint_noncollision firstNonzero
    · intro zero
      rw [zero, norm_zero, zero_div] at firstLower
      exact lowerPositive.not_le firstLower
    · intro equality
      have equal : (fourPointOddPart first).2 = (fourPointOddPart first).1 := (sub_eq_zero.mp equality).symm
      have ratio : ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ = 1 := by
        rw [equal, div_self (norm_ne_zero_iff.mpr firstNonzero)]
      rw [ratio] at firstUpper
      exact (firstUpper.trans_lt upperSmall).false
    · intro equality
      have equal : (fourPointOddPart first).2 = -(fourPointOddPart first).1 :=
        eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using equality)
      have ratio : ‖(fourPointOddPart first).2‖ / ‖(fourPointOddPart first).1‖ = 1 := by
        rw [equal, norm_neg, div_self (norm_ne_zero_iff.mpr firstNonzero)]
      rw [ratio] at firstUpper
      exact (firstUpper.trans_lt upperSmall).false
  have secondRatioLower : lower ≤ ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ := by
    simpa only [secondPositive, norm_one, div_one] using secondLower
  have secondRatioUpper : ‖(fourPointOddPart second).2‖ / ‖(fourPointOddPart second).1‖ ≤ upper := by
    simpa only [secondPositive, norm_one, div_one] using secondUpper
  have smallAbsolute : firstMoment + secondMoment < absoluteRadius * minimum :=
    momentSmall.trans_le (min_le_left _ _)
  have smallRelative : firstMoment + secondMoment < 2 * relativeRadius :=
    momentSmall.trans_le (min_le_right _ _)
  by_cases near : centralDifference + (firstMoment + secondMoment) / 4 ≤ relativeRadius
  · have actual := relativeEstimate coefficient (1 : ℂ) first second one_ne_zero secondPositive secondLower secondUpper
      firstCollision near
    have dilationOne (positions : FourPointConfiguration) : fourPointComplexDilation 1 positions = positions := by
      ext patch
      exact one_mul _
    rw [dilationOne first, dilationOne second, norm_one, div_one] at actual
    have enlarge : relativeBound ≤ bound := by
      dsimp only [bound]
      exact le_add_of_nonneg_right (by positivity)
    exact actual.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right enlarge (abs_nonneg coefficient)) (by positivity)) (by norm_num))
  · have far : relativeRadius / 2 ≤ centralDifference := by
      push_neg at near
      linarith
    have absolute (positions : FourPointConfiguration)
        (positiveNonzero : (fourPointOddPart positions).1 ≠ 0)
        (positiveMinimum : minimum ≤ ‖(fourPointOddPart positions).1‖)
        (ratioLower : lower ≤ ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖)
        (ratioUpper : ‖(fourPointOddPart positions).2‖ / ‖(fourPointOddPart positions).1‖ ≤ upper)
        (smallMoment : ‖fourPointSignedMoment positions‖ < absoluteRadius * minimum) :
        ‖fourPointOddInternalError coefficient positions‖ ≤
          (absoluteBound / minimum ^ 3) * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16 := by
      have actual := absoluteEstimate coefficient positions positiveNonzero ratioLower ratioUpper
        (smallMoment.trans_le (mul_le_mul_of_nonneg_left positiveMinimum absolutePositive.le))
      have denominator : 16 * minimum ^ 3 ≤ 16 * ‖(fourPointOddPart positions).1‖ ^ 3 := by
        gcongr
      have enlarged := actual.trans (div_le_div_of_nonneg_left (by positivity)
        (by positivity : 0 < 16 * minimum ^ 3) denominator)
      exact enlarged.trans_eq (by ring)
    have firstAbsolute := absolute first firstNonzero firstMinimum firstLower firstUpper
      (lt_of_le_of_lt (le_add_of_nonneg_right (norm_nonneg _)) smallAbsolute)
    have secondAbsolute := absolute second secondNonzero secondMinimum secondRatioLower secondRatioUpper
      (lt_of_le_of_lt (le_add_of_nonneg_left (norm_nonneg _)) smallAbsolute)
    have normDifference := norm_sub_norm_le (fourPointSignedMoment first) (fourPointSignedMoment second)
    have moments : firstMoment ^ 2 + secondMoment ^ 2 ≤
        (firstMoment + secondMoment) * differenceMoment + 2 * secondMoment ^ 2 := by
      have multiplied := mul_le_mul_of_nonneg_left normDifference
        (show 0 ≤ firstMoment + secondMoment by positivity)
      nlinarith only [multiplied]
    have farCost : 2 * secondMoment ^ 2 ≤ (4 / relativeRadius) * centralDifference * secondMoment ^ 2 := by
      have multiplied := mul_le_mul_of_nonneg_left far (show 0 ≤ 4 / relativeRadius by positivity)
      have coefficient : 2 ≤ (4 / relativeRadius) * centralDifference := by
        have cancel : (4 / relativeRadius) * (relativeRadius / 2) = 2 := by field_simp; ring
        rw [cancel] at multiplied
        exact multiplied
      nlinarith [sq_nonneg secondMoment]
    have scalar : firstMoment ^ 2 + secondMoment ^ 2 ≤
        (1 + 4 / relativeRadius) *
          ((firstMoment + secondMoment) * differenceMoment + centralDifference * secondMoment ^ 2) := by
      have extra : 0 ≤ (4 / relativeRadius) * ((firstMoment + secondMoment) * differenceMoment) := by positivity
      have centralNonnegative : 0 ≤ centralDifference * secondMoment ^ 2 := by positivity
      nlinarith only [moments, farCost, extra, centralNonnegative]
    have total := (norm_sub_le _ _).trans (add_le_add firstAbsolute secondAbsolute)
    have total' : ‖fourPointOddInternalError coefficient first - fourPointOddInternalError coefficient second‖ ≤
        (absoluteBound / minimum ^ 3) * |coefficient| / 16 * (firstMoment ^ 2 + secondMoment ^ 2) :=
      total.trans_eq (by ring)
    have actual := total'.trans (mul_le_mul_of_nonneg_left scalar
      (show 0 ≤ (absoluteBound / minimum ^ 3) * |coefficient| / 16 by positivity))
    have coefficientBound : absoluteBound / minimum ^ 3 * (1 + 4 / relativeRadius) ≤ bound := by
      dsimp only [bound]
      linarith
    apply actual.trans
    change _ ≤ bound * |coefficient| *
      ((firstMoment + secondMoment) * differenceMoment + centralDifference * secondMoment ^ 2) / 16
    have enlarged := mul_le_mul_of_nonneg_right coefficientBound
      (show 0 ≤ |coefficient| * ((firstMoment + secondMoment) * differenceMoment + centralDifference * secondMoment ^ 2) / 16 by positivity)
    convert enlarged using 1 <;> ring

end EulerNonuniqueness.Section6
