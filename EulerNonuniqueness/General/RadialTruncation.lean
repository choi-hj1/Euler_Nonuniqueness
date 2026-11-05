import Mathlib

noncomputable section

open Set Metric

def radialTruncation {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    (radius : ℝ) (position : space) : space :=
  (radius / max radius ‖position‖) • position

theorem radialTruncation_eq_self {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {radius : ℝ} (positive : 0 < radius) {position : space} (inside : ‖position‖ ≤ radius) :
    radialTruncation radius position = position := by
  simp only [radialTruncation, max_eq_left inside, div_self positive.ne', one_smul]

theorem norm_radialTruncation_le {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {radius : ℝ} (positive : 0 < radius) (position : space) :
    ‖radialTruncation radius position‖ ≤ radius := by
  have denominatorPositive : 0 < max radius ‖position‖ := positive.trans_le (le_max_left _ _)
  rw [radialTruncation, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg positive.le denominatorPositive.le)]
  calc
    _ ≤ (radius / max radius ‖position‖) * max radius ‖position‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _ = radius := div_mul_cancel₀ radius denominatorPositive.ne'

theorem dist_radialTruncation_le_of_denominator_order
    {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {radius : ℝ} (positive : 0 < radius) (first second : space)
    (ordered : max radius ‖second‖ ≤ max radius ‖first‖) :
    dist (radialTruncation radius first) (radialTruncation radius second) ≤ 2 * dist first second := by
  let firstDenominator := max radius ‖first‖
  let secondDenominator := max radius ‖second‖
  have firstPositive : 0 < firstDenominator := positive.trans_le (le_max_left _ _)
  have secondPositive : 0 < secondDenominator := positive.trans_le (le_max_left _ _)
  have firstCoefficient : 0 ≤ radius / firstDenominator := div_nonneg positive.le firstPositive.le
  have coefficientBound : radius / firstDenominator ≤ 1 :=
    (div_le_one firstPositive).mpr (le_max_left _ _)
  have coefficientOrder : radius / firstDenominator ≤ radius / secondDenominator :=
    div_le_div_of_nonneg_left positive.le secondPositive ordered
  have coefficientDifference :
      |radius / firstDenominator - radius / secondDenominator| * ‖second‖ ≤
        firstDenominator - secondDenominator := by
    rw [abs_of_nonpos (sub_nonpos.mpr coefficientOrder), neg_sub]
    calc
      _ ≤ (radius / secondDenominator - radius / firstDenominator) * secondDenominator :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (sub_nonneg.mpr coefficientOrder)
      _ = (radius / firstDenominator) * (firstDenominator - secondDenominator) := by
        field_simp [firstPositive.ne', secondPositive.ne']
        ring
      _ ≤ firstDenominator - secondDenominator := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right coefficientBound (sub_nonneg.mpr ordered)
  have denominatorDifference : firstDenominator - secondDenominator ≤ ‖first - second‖ := by
    apply sub_le_iff_le_add.mpr
    apply max_le
    · exact (le_max_left radius ‖second‖).trans (le_add_of_nonneg_left (norm_nonneg _))
    · calc
        ‖first‖ ≤ ‖first - second‖ + ‖second‖ := by
          simpa only [sub_add_cancel] using norm_add_le (first - second) second
        _ ≤ ‖first - second‖ + secondDenominator := add_le_add_left (le_max_right radius ‖second‖) _
  have decomposition : radialTruncation radius first - radialTruncation radius second =
      (radius / firstDenominator) • (first - second) +
        (radius / firstDenominator - radius / secondDenominator) • second := by
    dsimp only [radialTruncation, firstDenominator, secondDenominator]
    rw [smul_sub, sub_smul]
    abel
  rw [dist_eq_norm, decomposition, dist_eq_norm]
  have triangle := norm_add_le ((radius / firstDenominator) • (first - second))
    ((radius / firstDenominator - radius / secondDenominator) • second)
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg firstCoefficient] at triangle
  have firstTerm := mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg (first - second))
  nlinarith

theorem lipschitzWith_radialTruncation {space : Type*} [NormedAddCommGroup space] [NormedSpace ℝ space]
    {radius : ℝ} (positive : 0 < radius) : LipschitzWith 2 (radialTruncation (space := space) radius) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rcases le_total (max radius ‖second‖) (max radius ‖first‖) with ordered | reverse
  · exact dist_radialTruncation_le_of_denominator_order positive first second ordered
  · simpa only [dist_comm] using dist_radialTruncation_le_of_denominator_order positive second first reverse
