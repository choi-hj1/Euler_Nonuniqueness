import EulerNonuniqueness.Section4.ReferenceShapeChartSafety
import EulerNonuniqueness.Section6.ReferenceCentroidShapeEquation

noncomputable section

open Set

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_regularized_shape_equation_on_reference_tube {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (positiveContinuous : ContinuousOn (fun current => positiveHalfDiagonal family.patchMotion current index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun current => negativeHalfDiagonal family.patchMotion current index) (Icc 0 horizon))
    (initialUpper : 0 < (negativeHalfDiagonal family.patchMotion 0 index / positiveHalfDiagonal family.patchMotion 0 index).im)
    (small : ∀ current ∈ Icc 0 horizon,
      |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
        (negativeHalfDiagonal family.patchMotion current index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
        (negativeHalfDiagonal family.patchMotion current index)).2| ≤ 1 / 4)
    (differenceLower : ∀ current ∈ Icc 0 horizon,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion current index) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    HasDerivWithinAt (fun current => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
      (Section6.shapeChartVelocity (coefficient / diagonalDifference family.patchMotion time index)
          (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) +
        Section6.pointShapeForcing (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index)
          (Section6.fourPointTotalOddForcing coefficient positions
            (quadrupoleCentroidForcing scales family.patchMotion time index)).1
          (Section6.fourPointTotalOddForcing coefficient positions
            (quadrupoleCentroidForcing scales family.patchMotion time index)).2) (Icc 0 horizon) time := by
  have safe := reference_coherent_shape_chart_safe_on_interval family.patchMotion index positiveContinuous
    negativeContinuous initialUpper small
  have regularized := reference_regularized_shape_eq_paper_on_interval scales family.patchMotion index positiveContinuous
    negativeContinuous initialUpper small differenceLower
  have derivative := family.centroid_coherent_shape_equation_of_reference_chart evolution inside index
    pathInside material (small time inside)
  rw [(safe time inside).2] at derivative
  apply derivative.hasDerivWithinAt.congr_of_mem
  · intro current currentInside
    exact (regularized current currentInside).trans (safe current currentInside).2.symm
  · exact inside

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
