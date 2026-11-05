import EulerNonuniqueness.Section4.ReferenceMechanicalMonitorBounds
import EulerNonuniqueness.Section4.MovingReferenceMechanicalMonitorBounds

noncomputable section

namespace EulerNonuniqueness.Paper

theorem reference_radial_branch_monitors_strict_of_coordinate_box
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    (scales : Scales) {shapeRadius gap margin shapeStop radius : ℝ}
    (state : MovingContourState (count * 4)) (index : Fin count)
    (radiusSmall : radius ≤ 1 / 8)
    (unstableBound : |(movingReferenceShapeCoordinates scales state index).1| ≤ radius)
    (stableBound : |(movingReferenceShapeCoordinates scales state index).2| ≤ radius)
    (diagonalBound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.diagonal index) ≤ 0)
    (branchBound : referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.branch index) ≤ 0) :
    referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.radial index) < 0 ∧
    referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop state (.branch index) < 0 := by
  have radial := movingReferenceRadialObservable_improvement scales state index radiusSmall unstableBound stableBound
  have diagonal := (referenceMechanicalMonitor_diagonal index diagonalBound).1
  have lower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖(state.2.1 (finProdFinEquiv (index, 0)) - state.2.1 (finProdFinEquiv (index, 1))) / 2‖ ^ 2 := by
    change scales.length (index.val + 1) ^ 2 / 2 ≤ ‖movingReferencePositiveDiagonal state index‖ ^ 2
    dsimp only [movingReferenceDiagonalDifference] at diagonal
    nlinarith [sq_nonneg ‖movingReferenceNegativeDiagonal state index‖]
  have branch := movingReferenceRatioImaginary_improvement scales state index lower
    (show |(movingReferenceShapeCoordinates scales state index).1| +
        |(movingReferenceShapeCoordinates scales state index).2| ≤ 1 / 4 by linarith)
    (by linarith [referenceMechanicalMonitor_branch index branchBound])
  constructor
  · change |movingReferenceRadialObservable scales state index| - 1 / 2 < 0
    linarith
  · change 1 / 16 - movingReferenceRatioImaginary scales state index < 0
    linarith

end EulerNonuniqueness.Paper
