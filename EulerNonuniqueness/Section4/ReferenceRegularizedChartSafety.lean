import EulerNonuniqueness.Section4.RegularizedShapeCoordinates
import EulerNonuniqueness.Section6.PaperShapeBranch
import EulerNonuniqueness.Section6.ReferenceChartImaginaryGap
import EulerNonuniqueness.Section4.ReferenceInitialInvariants
import EulerNonuniqueness.Section4.InitialRegularizedShape

noncomputable section

namespace EulerNonuniqueness.Paper

theorem reference_regularized_chart_imaginary_improvement {count : ℕ} (scales : Scales)
    (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index)
    (imaginaryLower : (1 / 16 : ℝ) ≤
      (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im)
    (small :
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4) :
    (1 / 8 : ℝ) ≤ (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im ∧
      Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) := by
  have denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    dsimp only [diagonalDifference] at differenceLower
    nlinarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  have upper : 0 < (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im := by
    linarith
  have regularized := regularizedShapeCoordinates_eq_paper motion time index denominatorLower imaginaryLower
  have coherent := pointShapeChart_eq_paper_shape_of_upper motion time index upper
  have identity := coherent.trans regularized.symm
  refine ⟨Section6.pointShapeChart_reference_imaginary_gap _ _ ?_ upper, identity⟩
  rwa [identity]

theorem FinitePatchEvolution.reference_initial_ratio_im_lower
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon threshold : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonNonnegative : 0 ≤ horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) {phase unstable : Fin count → ℝ}
    (initial : ReferenceInitialDisks scales motion phase unstable threshold)
    (thresholdSmall : threshold ≤ 1 / 2) (index : Fin count) :
    (1 / 8 : ℝ) ≤ (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im := by
  have diagonals := evolution.reference_initial_diagonals horizonNonnegative amplitudePositive frequencyPositive ratioPositive initial index
  rw [diagonals.1, diagonals.2]
  exact initialDiagonals_ratio_im_lower scales _ _ _ ((initial index).1.trans thresholdSmall)

end EulerNonuniqueness.Paper
