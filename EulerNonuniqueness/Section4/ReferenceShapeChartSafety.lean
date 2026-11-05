import EulerNonuniqueness.Section6.ReferenceChartImaginaryGap
import EulerNonuniqueness.Section6.PaperShapeBranch
import EulerNonuniqueness.Section4.RegularizedShapeCoordinates

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem reference_coherent_shape_chart_safe_on_interval {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) {horizon : ℝ}
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4) :
    ∀ time ∈ Icc 0 horizon,
      (1 / 8 : ℝ) ≤ (negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index).im ∧
      Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  have positiveNonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      positiveHalfDiagonal motion time index ≠ 0 :=
    (Section6.pointShapeChart_reference_annulus _ _ (small time inside)).1
  have left (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ((negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) ^ 2).re < 0 := by
    obtain ⟨positive, negative, _, _⟩ := Section6.pointShapeChart_reference_annulus _ _ (small time inside)
    exact Section6.pointShapeChart_leftHalfPlane_of_small positive negative (small time inside)
  have upper := Section6.upperHalfPlane_of_initial_and_square_left
    (negativeContinuous.div positiveContinuous positiveNonzero) initialUpper left
  intro time inside
  exact ⟨Section6.pointShapeChart_reference_imaginary_gap _ _ (small time inside) (upper time inside),
    pointShapeChart_eq_paper_shape_of_upper motion time index (upper time inside)⟩

theorem reference_regularized_shape_eq_paper_on_interval {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (index : Fin count) {horizon : ℝ}
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4)
    (differenceLower : ∀ time ∈ Icc 0 horizon,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference motion time index) :
    ∀ time ∈ Icc 0 horizon,
      regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
          (unstableShape motion time index, stableShape motion time index) := by
  have safe := reference_coherent_shape_chart_safe_on_interval motion index positiveContinuous negativeContinuous initialUpper small
  intro time inside
  apply regularizedShapeCoordinates_eq_paper
  · have lower := differenceLower time inside
    unfold diagonalDifference at lower
    linarith [sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  · exact (by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans (safe time inside).1

end EulerNonuniqueness.Paper
