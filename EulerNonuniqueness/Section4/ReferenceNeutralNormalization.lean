import EulerNonuniqueness.Section4.ReferenceNeutralForcingScale

noncomputable section

open EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem reference_normalized_signed_moment_small {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count) {memory radius : ℝ}
    (memoryNonnegative : 0 ≤ memory) (radiusPositive : 0 < radius)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (asymmetryBound : ‖centroidAsymmetry motion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2)
    (lengthSmall : scales.length (index.val + 1) < radius / (8 * (memory + 1))) :
    ‖fourPointSignedMoment (fun patch => patchCentroid motion time index patch)‖ <
      radius * ‖positiveHalfDiagonal motion time index‖ := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have diagonalLower : scales.length (index.val + 1) / 2 ≤ ‖positiveHalfDiagonal motion time index‖ := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖,
      norm_nonneg (positiveHalfDiagonal motion time index)]
  have denominatorPositive : 0 < 8 * (memory + 1) := by positivity
  have small := (lt_div_iff₀ denominatorPositive).mp lengthSmall
  have coefficientSmall : 8 * memory * scales.length (index.val + 1) < radius := by
    nlinarith
  have multiplied := mul_lt_mul_of_pos_right coefficientSmall lengthPositive
  rw [centroid_fourPointSignedMoment, norm_mul]
  have normFour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  rw [normFour]
  have normBound := mul_le_mul_of_nonneg_left asymmetryBound (by norm_num : (0 : ℝ) ≤ 4)
  have diagonalBound := mul_le_mul_of_nonneg_left diagonalLower radiusPositive.le
  nlinarith

end EulerNonuniqueness.Paper
