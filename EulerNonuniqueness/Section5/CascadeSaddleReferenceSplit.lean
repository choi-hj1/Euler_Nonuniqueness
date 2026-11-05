import EulerNonuniqueness.Section5.CascadeSaddlePointRemainder

noncomputable section

namespace EulerNonuniqueness.Paper

theorem relativeStraightenedSaddlePointBudget_le_reference_split
    {count : ℕ} (scales : Scales) (motion : Fin 2 → PatchMotion count)
    (graph coordinate : ℝ → ℝ) (constant referenceConstant : ℝ)
    (index : Fin count) (time : ℝ) :
    let first := referenceStraightenedShape (motion 0) graph coordinate index time
    let second := referenceStraightenedShape (motion 1) graph coordinate index time
    let difference := |first.1 - second.1| + |first.2 - second.2|
    let referenceSize := |second.1| + |second.2|
    let dilationDifference := |diagonalDifference (motion 0) time index -
      diagonalDifference (motion 1) time index| / scales.length (index.val + 1) ^ 2
    let referenceDefect := |diagonalDifference (motion 1) time index /
      scales.length (index.val + 1) ^ 2 - 1|
    relativeStraightenedSaddlePointBudget scales motion graph coordinate constant referenceConstant index time ≤
      2 * Real.sqrt 2 *
        (2 * |scales.omega (index.val + 1)| * (referenceDefect + dilationDifference) * difference +
          4 * |scales.omega (index.val + 1)| * dilationDifference * referenceSize) +
        2 * |scales.omega (index.val + 1)| *
          (constant * difference * (|first.2 - second.2| + |second.1| + |second.2|)) +
        (4 * |scales.omega (index.val + 1)| * dilationDifference) * (referenceConstant * referenceSize) := by
  let length := scales.length (index.val + 1)
  let firstDilation := diagonalDifference (motion 0) time index / length ^ 2
  let secondDilation := diagonalDifference (motion 1) time index / length ^ 2
  have differenceIdentity : |firstDilation - secondDilation| =
      |diagonalDifference (motion 0) time index - diagonalDifference (motion 1) time index| / length ^ 2 := by
    dsimp only [firstDilation, secondDilation]
    rw [← sub_div, abs_div, abs_of_pos (sq_pos_of_pos (scales.length_pos _))]
  have defect : |firstDilation - 1| ≤ |secondDilation - 1| + |firstDilation - secondDilation| := by
    have identity : firstDilation - 1 = (secondDilation - 1) + (firstDilation - secondDilation) := by ring
    rw [identity]
    exact abs_add _ _
  dsimp only [relativeStraightenedSaddlePointBudget]
  rw [← differenceIdentity]
  apply add_le_add_right
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left defect (by positivity)

end EulerNonuniqueness.Paper
