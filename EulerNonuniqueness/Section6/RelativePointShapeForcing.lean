import EulerNonuniqueness.Section6.PointShapeForcingBound

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem pointShapeForcing_logDifference_norm_le
    (positive negative positiveForcing negativeForcing : ℂ) :
    ‖pointShapeForcing positive negative positiveForcing negativeForcing‖ ≤
      (pointShapeRatio positive negative / rhombusRatio + 1) *
        ‖negativeForcing / negative - positiveForcing / positive‖ := by
  let difference := negativeForcing / negative - positiveForcing / positive
  let ratio := pointShapeRatio positive negative / rhombusRatio
  have ratioNonnegative : 0 ≤ ratio :=
    div_nonneg (by dsimp [pointShapeRatio]; positivity) rhombusRatio_pos.le
  have sqrtLower : 1 ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have component (imaginary : ℝ) (imaginaryBound : |imaginary| ≤ ‖difference‖) :
      |ratio * difference.re + imaginary / Real.sqrt 2| ≤ (ratio + 1) * ‖difference‖ := by
    calc
      _ ≤ |ratio * difference.re| + |imaginary / Real.sqrt 2| := abs_add_le _ _
      _ = ratio * |difference.re| + |imaginary| / Real.sqrt 2 := by
        rw [abs_mul, abs_of_nonneg ratioNonnegative, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ ratio * ‖difference‖ + ‖difference‖ := add_le_add
        (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm difference) ratioNonnegative)
        ((div_le_self (abs_nonneg imaginary) sqrtLower).trans imaginaryBound)
      _ = _ := by ring
  have identity : pointShapeForcing positive negative positiveForcing negativeForcing =
      (ratio * difference.re + difference.im / Real.sqrt 2,
        ratio * difference.re + (-difference.im) / Real.sqrt 2) := by
    ext <;> dsimp [pointShapeForcing, ratio, difference] <;> ring
  rw [identity]
  exact max_le (component difference.im (Complex.abs_im_le_norm difference))
    (component (-difference.im) (by simpa only [abs_neg] using Complex.abs_im_le_norm difference))

theorem pointShapeForcing_relative_norm_le
    {positive negative positiveForcing negativeForcing : ℂ} {strainBound ratioBound : ℝ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (strainNonnegative : 0 ≤ strainBound)
    (positiveBound : ‖positiveForcing‖ ≤ strainBound * ‖positive‖)
    (negativeBound : ‖negativeForcing‖ ≤ strainBound * ‖negative‖)
    (ratioEstimate : pointShapeRatio positive negative ≤ ratioBound * rhombusRatio) :
    ‖pointShapeForcing positive negative positiveForcing negativeForcing‖ ≤
      2 * (ratioBound + 1) * strainBound := by
  have positiveNorm : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have negativeNorm : 0 < ‖negative‖ := norm_pos_iff.mpr negativeNonzero
  have ratioEstimate' : pointShapeRatio positive negative / rhombusRatio ≤ ratioBound :=
    (div_le_iff₀ rhombusRatio_pos).mpr ratioEstimate
  have ratioNonnegative : 0 ≤ pointShapeRatio positive negative / rhombusRatio := by
    exact div_nonneg (by dsimp [pointShapeRatio]; positivity) rhombusRatio_pos.le
  have differenceBound : ‖negativeForcing / negative - positiveForcing / positive‖ ≤ 2 * strainBound := by
    calc
      _ ≤ ‖negativeForcing / negative‖ + ‖positiveForcing / positive‖ := norm_sub_le _ _
      _ = ‖negativeForcing‖ / ‖negative‖ + ‖positiveForcing‖ / ‖positive‖ := by rw [norm_div, norm_div]
      _ ≤ strainBound + strainBound := add_le_add
        ((div_le_iff₀ negativeNorm).mpr negativeBound)
        ((div_le_iff₀ positiveNorm).mpr positiveBound)
      _ = _ := by ring
  calc
    _ ≤ (pointShapeRatio positive negative / rhombusRatio + 1) *
        ‖negativeForcing / negative - positiveForcing / positive‖ :=
      pointShapeForcing_logDifference_norm_le _ _ _ _
    _ ≤ (pointShapeRatio positive negative / rhombusRatio + 1) * (2 * strainBound) :=
      mul_le_mul_of_nonneg_left differenceBound (by positivity)
    _ ≤ (ratioBound + 1) * (2 * strainBound) :=
      mul_le_mul_of_nonneg_right (add_le_add_right ratioEstimate' 1) (by positivity)
    _ = _ := by ring

theorem pointShapeForcing_odd_field_lipschitz_norm_le
    (positions : FourPointConfiguration) (field : ℂ → ℂ) {strainBound ratioBound : ℝ}
    (strainNonnegative : 0 ≤ strainBound)
    (positiveNonzero : (fourPointOddPart positions).1 ≠ 0)
    (negativeNonzero : (fourPointOddPart positions).2 ≠ 0)
    (positivePair : ‖field (positions 0) - field (positions 1)‖ ≤ strainBound * ‖positions 0 - positions 1‖)
    (negativePair : ‖field (positions 2) - field (positions 3)‖ ≤ strainBound * ‖positions 2 - positions 3‖)
    (ratioEstimate : pointShapeRatio (fourPointOddPart positions).1 (fourPointOddPart positions).2 ≤
      ratioBound * rhombusRatio) :
    ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
      (fourPointOddPart (fun label => field (positions label))).1
      (fourPointOddPart (fun label => field (positions label))).2‖ ≤
        2 * (ratioBound + 1) * strainBound := by
  apply pointShapeForcing_relative_norm_le positiveNonzero negativeNonzero strainNonnegative
  · dsimp only [fourPointOddPart]
    simp only [norm_div, Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right positivePair (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · dsimp only [fourPointOddPart]
    simp only [norm_div, Complex.norm_ofNat]
    exact (div_le_div_of_nonneg_right negativePair (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  · exact ratioEstimate

end EulerNonuniqueness.Section6
