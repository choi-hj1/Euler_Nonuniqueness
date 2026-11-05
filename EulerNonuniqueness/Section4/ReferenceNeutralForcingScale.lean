import EulerNonuniqueness.Section1.IndividualCirculationStrain
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing

noncomputable section

open EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

theorem reference_internal_shape_cost_le_strain {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) {bound memory : ℝ}
    (boundNonnegative : 0 ≤ bound) (memoryNonnegative : 0 ≤ memory)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference motion time index)
    (asymmetryBound : ‖centroidAsymmetry motion time index‖ ≤
      memory * scales.length (index.val + 1) ^ 2) :
    bound * |scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2| *
        ‖fourPointSignedMoment (fun patch => patchCentroid motion time index patch)‖ ^ 2 /
          (16 * ‖positiveHalfDiagonal motion time index‖ ^ 4) ≤
      (2 * bound * memory ^ 2 / Real.pi) * scales.strain := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have omegaPositive := scales.omega_pos (zero_lt_one.trans_le frequencyBound)
    (show 0 < scales.ratio by linarith) (index.val + 1)
  have diagonalLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have diagonalPositive : 0 < ‖positiveHalfDiagonal motion time index‖ := by
    nlinarith [norm_nonneg (positiveHalfDiagonal motion time index)]
  have fourthLower : scales.length (index.val + 1) ^ 4 / 4 ≤
      ‖positiveHalfDiagonal motion time index‖ ^ 4 := by
    nlinarith [sq_nonneg (‖positiveHalfDiagonal motion time index‖ ^ 2 -
      scales.length (index.val + 1) ^ 2 / 2)]
  have momentSquare : ‖centroidAsymmetry motion time index‖ ^ 2 ≤
      memory ^ 2 * scales.length (index.val + 1) ^ 4 := by
    have bound := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg memoryNonnegative (sq_nonneg _))).mpr asymmetryBound
    convert bound using 1 <;> ring
  rw [centroid_fourPointSignedMoment, norm_mul]
  have normFour : ‖(4 : ℂ)‖ = (4 : ℝ) := by norm_num
  rw [normFour]
  rw [abs_of_pos (mul_pos omegaPositive (sq_pos_of_pos lengthPositive))]
  have cancellation : bound * (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) *
      (4 * ‖centroidAsymmetry motion time index‖) ^ 2 /
        (16 * ‖positiveHalfDiagonal motion time index‖ ^ 4) =
      bound * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 *
        ‖centroidAsymmetry motion time index‖ ^ 2 /
          ‖positiveHalfDiagonal motion time index‖ ^ 4 := by ring
  rw [cancellation]
  calc
    _ ≤ bound * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 *
        (memory ^ 2 * scales.length (index.val + 1) ^ 4) /
          ‖positiveHalfDiagonal motion time index‖ ^ 4 := by gcongr
    _ ≤ bound * scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 *
        (memory ^ 2 * scales.length (index.val + 1) ^ 4) /
          (scales.length (index.val + 1) ^ 4 / 4) := by gcongr
    _ = (4 * bound * memory ^ 2) *
        (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) := by
      field_simp
      <;> ring
    _ ≤ (4 * bound * memory ^ 2) * (scales.strain / (2 * Real.pi)) := by
      exact mul_le_mul_of_nonneg_left
        (scales.omega_length_sq_le_strain frequencyBound ratioBound alphaPositive index.val) (by positivity)
    _ = _ := by ring

end EulerNonuniqueness.Paper
