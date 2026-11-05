import EulerNonuniqueness.Section4.ReferenceConfinement
import EulerNonuniqueness.Section4.InitialRhombusSeparation

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000

theorem halfDiagonals_lower_and_ratio_of_reference_shape {count : ℕ}
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) {length : ℝ}
    (lengthPositive : 0 < length)
    (differenceLower : length ^ 2 / 2 ≤ diagonalDifference motion time index)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2) :
    length / 2 ≤ ‖positiveHalfDiagonal motion time index‖ ∧
      length / 8 ≤ ‖negativeHalfDiagonal motion time index‖ ∧
      ‖negativeHalfDiagonal motion time index‖ ≤ (3 / 4 : ℝ) * ‖positiveHalfDiagonal motion time index‖ := by
  have positiveSquare : 0 < ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    unfold diagonalDifference at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have radialLower := (abs_le.mp radialSmall).1
  have radialUpper := (abs_le.mp radialSmall).2
  unfold radialShape at radialLower radialUpper
  have ratioLower : (1 / 16 : ℝ) ≤ ‖negativeHalfDiagonal motion time index‖ ^ 2 /
      ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    have lower := (le_div_iff₀ reference_rhombusRatio_bounds.1).mp radialLower
    linarith [reference_rhombusRatio_lower]
  have ratioUpper : ‖negativeHalfDiagonal motion time index‖ ^ 2 /
      ‖positiveHalfDiagonal motion time index‖ ^ 2 ≤ (3 / 8 : ℝ) := by
    have upper := (div_le_iff₀ reference_rhombusRatio_bounds.1).mp radialUpper
    linarith [reference_rhombusRatio_bounds.2]
  have lowerSquare := (le_div_iff₀ positiveSquare).mp ratioLower
  have upperSquare := (div_le_iff₀ positiveSquare).mp ratioUpper
  have positiveLower : length / 2 ≤ ‖positiveHalfDiagonal motion time index‖ := by
    unfold diagonalDifference at differenceLower
    nlinarith [norm_nonneg (positiveHalfDiagonal motion time index), sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  refine ⟨positiveLower, ?_, ?_⟩
  · nlinarith [norm_nonneg (negativeHalfDiagonal motion time index)]
  · nlinarith [norm_nonneg (positiveHalfDiagonal motion time index), norm_nonneg (negativeHalfDiagonal motion time index)]

private theorem mixed_centroid_offset_lower (positive negative asymmetry : ℂ) {length : ℝ}
    (lengthPositive : 0 < length) (positiveLower : length / 2 ≤ ‖positive‖)
    (negativeUpper : ‖negative‖ ≤ (3 / 4 : ℝ) * ‖positive‖)
    (asymmetrySmall : ‖asymmetry‖ ≤ length / 64) :
    length / 16 ≤ ‖2 * asymmetry + positive + negative‖ := by
  have triangle : ‖positive‖ ≤ ‖2 * asymmetry + positive + negative‖ + 2 * ‖asymmetry‖ + ‖negative‖ := by
    have identity : positive = (2 * asymmetry + positive + negative) - 2 * asymmetry - negative := by ring
    calc
      _ = ‖(2 * asymmetry + positive + negative) - 2 * asymmetry - negative‖ := by rw [← identity]
      _ ≤ (‖2 * asymmetry + positive + negative‖ + ‖2 * asymmetry‖) + ‖negative‖ :=
        (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
      _ = _ := by rw [norm_mul]; norm_num
  linarith

def quadrupoleCentroidOffset (positive negative asymmetry : ℂ) (patch : Fin 4) : ℂ :=
  if patch = 0 then asymmetry + positive else if patch = 1 then asymmetry - positive
  else if patch = 2 then -asymmetry + negative else -asymmetry - negative

theorem quadrupoleCentroidOffset_pair_lower (positive negative asymmetry : ℂ) {length : ℝ}
    (lengthPositive : 0 < length) (positiveLower : length / 2 ≤ ‖positive‖)
    (negativeLower : length / 8 ≤ ‖negative‖)
    (negativeUpper : ‖negative‖ ≤ (3 / 4 : ℝ) * ‖positive‖)
    (asymmetrySmall : ‖asymmetry‖ ≤ length / 64)
    (first second : Fin 4) (different : first ≠ second) :
    length / 16 ≤ ‖quadrupoleCentroidOffset positive negative asymmetry first -
      quadrupoleCentroidOffset positive negative asymmetry second‖ := by
  have positivePair : length / 16 ≤ ‖2 * positive‖ := by
    rw [norm_mul]
    norm_num
    linarith
  have negativePair : length / 16 ≤ ‖2 * negative‖ := by
    rw [norm_mul]
    norm_num
    linarith
  have mixedFirst := mixed_centroid_offset_lower positive negative asymmetry lengthPositive positiveLower negativeUpper asymmetrySmall
  have mixedSecond := mixed_centroid_offset_lower positive (-negative) asymmetry lengthPositive positiveLower
    (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have mixedThird := mixed_centroid_offset_lower (-positive) negative asymmetry lengthPositive
    (by simpa only [norm_neg] using positiveLower) (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have mixedFourth := mixed_centroid_offset_lower (-positive) (-negative) asymmetry lengthPositive
    (by simpa only [norm_neg] using positiveLower) (by simpa only [norm_neg] using negativeUpper) asymmetrySmall
  have negativePositivePair : length / 16 ≤ ‖-(2 * positive)‖ := by simpa only [norm_neg] using positivePair
  have negativeNegativePair : length / 16 ≤ ‖-(2 * negative)‖ := by simpa only [norm_neg] using negativePair
  have negativeMixedFirst : length / 16 ≤ ‖-(2 * asymmetry + positive + negative)‖ := by simpa only [norm_neg] using mixedFirst
  have negativeMixedSecond : length / 16 ≤ ‖-(2 * asymmetry + positive + -negative)‖ := by simpa only [norm_neg] using mixedSecond
  have negativeMixedThird : length / 16 ≤ ‖-(2 * asymmetry + -positive + negative)‖ := by simpa only [norm_neg] using mixedThird
  have negativeMixedFourth : length / 16 ≤ ‖-(2 * asymmetry + -positive + -negative)‖ := by simpa only [norm_neg] using mixedFourth
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

theorem patchCentroid_pair_lower_of_reference_shape {count : ℕ}
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) {length : ℝ}
    (lengthPositive : 0 < length)
    (differenceLower : length ^ 2 / 2 ≤ diagonalDifference motion time index)
    (radialSmall : |radialShape motion time index| ≤ 1 / 2)
    (asymmetrySmall : ‖centroidAsymmetry motion time index‖ ≤ length / 64)
    (first second : Fin 4) (different : first ≠ second) :
    length / 16 ≤ ‖patchCentroid motion time index first - patchCentroid motion time index second‖ := by
  obtain ⟨positiveLower, negativeLower, negativeUpper⟩ :=
    halfDiagonals_lower_and_ratio_of_reference_shape motion time index lengthPositive differenceLower radialSmall
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
  exact quadrupoleCentroidOffset_pair_lower _ _ _ lengthPositive positiveLower negativeLower negativeUpper asymmetrySmall first second different

end EulerNonuniqueness.Paper
