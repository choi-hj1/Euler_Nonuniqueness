import EulerNonuniqueness.Section4.ReferenceSiblingSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

private theorem rhombus_mixed_centroid_offset_strict (positive negative asymmetry : ℂ) {length : ℝ}
    (lengthPositive : 0 < length) (positiveLower : 2 * length / 3 ≤ ‖positive‖)
    (negativeUpper : ‖negative‖ ≤ (3 / 4 : ℝ) * ‖positive‖)
    (asymmetrySmall : ‖asymmetry‖ ≤ length / 64) :
    length / 8 < ‖2 * asymmetry + positive + negative‖ := by
  have triangle : ‖positive‖ ≤ ‖2 * asymmetry + positive + negative‖ + 2 * ‖asymmetry‖ + ‖negative‖ := by
    have identity : positive = (2 * asymmetry + positive + negative) - 2 * asymmetry - negative := by ring
    calc
      _ = ‖(2 * asymmetry + positive + negative) - 2 * asymmetry - negative‖ := by rw [← identity]
      _ ≤ (‖2 * asymmetry + positive + negative‖ + ‖2 * asymmetry‖) + ‖negative‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ = _ := by rw [norm_mul]; norm_num
  linarith

theorem quadrupoleCentroidOffset_pair_strict_eighth (positive negative asymmetry : ℂ) {length : ℝ}
    (lengthPositive : 0 < length) (positiveLower : 2 * length / 3 ≤ ‖positive‖)
    (negativeLower : length / 8 ≤ ‖negative‖)
    (negativeUpper : ‖negative‖ ≤ (3 / 4 : ℝ) * ‖positive‖)
    (asymmetrySmall : ‖asymmetry‖ ≤ length / 64)
    (first second : Fin 4) (different : first ≠ second) :
    length / 8 < ‖quadrupoleCentroidOffset positive negative asymmetry first -
      quadrupoleCentroidOffset positive negative asymmetry second‖ := by
  have positivePair : length / 8 < ‖2 * positive‖ := by
    rw [norm_mul]
    norm_num
    linarith
  have negativePair : length / 8 < ‖2 * negative‖ := by
    rw [norm_mul]
    norm_num
    linarith
  have mixedFirst := rhombus_mixed_centroid_offset_strict positive negative asymmetry lengthPositive positiveLower negativeUpper asymmetrySmall
  have mixedSecond := rhombus_mixed_centroid_offset_strict positive (-negative) asymmetry lengthPositive positiveLower
    (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have mixedThird := rhombus_mixed_centroid_offset_strict (-positive) negative asymmetry lengthPositive
    (by simpa only [norm_neg] using positiveLower) (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have mixedFourth := rhombus_mixed_centroid_offset_strict (-positive) (-negative) asymmetry lengthPositive
    (by simpa only [norm_neg] using positiveLower) (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have negativePositivePair : length / 8 < ‖-(2 * positive)‖ := by simpa only [norm_neg] using positivePair
  have negativeNegativePair : length / 8 < ‖-(2 * negative)‖ := by simpa only [norm_neg] using negativePair
  have negativeMixedFirst : length / 8 < ‖-(2 * asymmetry + positive + negative)‖ := by simpa only [norm_neg] using mixedFirst
  have negativeMixedSecond : length / 8 < ‖-(2 * asymmetry + positive + -negative)‖ := by simpa only [norm_neg] using mixedSecond
  have negativeMixedThird : length / 8 < ‖-(2 * asymmetry + -positive + negative)‖ := by simpa only [norm_neg] using mixedThird
  have negativeMixedFourth : length / 8 < ‖-(2 * asymmetry + -positive + -negative)‖ := by simpa only [norm_neg] using mixedFourth
  fin_cases first <;> fin_cases second
  all_goals first | exact (different rfl).elim | skip
  all_goals norm_num [quadrupoleCentroidOffset, Fin.ext_iff]
  all_goals solve
    | convert positivePair using 1 <;> congr 1 <;> ring
    | convert negativePair using 1 <;> congr 1 <;> ring
    | convert negativePositivePair using 1 <;> congr 1 <;> ring
    | convert negativeNegativePair using 1 <;> congr 1 <;> ring
    | convert mixedFirst using 1 <;> congr 1 <;> ring
    | convert mixedSecond using 1 <;> congr 1 <;> ring
    | convert mixedThird using 1 <;> congr 1 <;> ring
    | convert mixedFourth using 1 <;> congr 1 <;> ring
    | convert negativeMixedFirst using 1 <;> congr 1 <;> ring
    | convert negativeMixedSecond using 1 <;> congr 1 <;> ring
    | convert negativeMixedThird using 1 <;> congr 1 <;> ring
    | convert negativeMixedFourth using 1 <;> congr 1 <;> ring

theorem patchCentroid_pair_strict_eighth_of_rhombus_shape {count : ℕ}
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) {length : ℝ}
    (lengthPositive : 0 < length)
    (differenceLower : length ^ 2 / 2 ≤ diagonalDifference motion time index)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ length / 64)
    (first second : Fin 4) (different : first ≠ second) :
    length / 8 < ‖patchCentroid motion time index first - patchCentroid motion time index second‖ := by
  obtain ⟨positiveLower, negativeLower, negativeUpper⟩ :=
    halfDiagonals_lower_and_ratio_of_reference_shape motion time index lengthPositive differenceLower radialSmall
  have sharperPositive : 2 * length / 3 ≤ ‖positiveHalfDiagonal motion time index‖ := by
    unfold diagonalDifference at differenceLower
    nlinarith [norm_nonneg (positiveHalfDiagonal motion time index), sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have identity : patchCentroid motion time index first - patchCentroid motion time index second =
      quadrupoleCentroidOffset (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
        (centroidAsymmetry motion time index) first -
      quadrupoleCentroidOffset (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
        (centroidAsymmetry motion time index) second := by
    calc
      _ = (patchCentroid motion time index first - quadrupoleCenter motion time index) -
          (patchCentroid motion time index second - quadrupoleCenter motion time index) := by ring
      _ = _ := by rw [patchCentroid_sub_quadrupoleCenter, patchCentroid_sub_quadrupoleCenter]; rfl
  rw [identity]
  exact quadrupoleCentroidOffset_pair_strict_eighth _ _ _ lengthPositive sharperPositive negativeLower negativeUpper asymmetrySmall first second different


end EulerNonuniqueness.Paper

