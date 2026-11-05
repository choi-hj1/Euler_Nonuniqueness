import EulerNonuniqueness.Section4.ReferenceRegularizedChartSafety
import EulerNonuniqueness.Section6.ReferenceCentroidShapeEquation

noncomputable section

open Set EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

def referencePointShapeForcing {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ × ℝ :=
  pointShapeForcing (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
    (fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid motion time index patch)
      (quadrupoleCentroidForcing scales motion time index)).1
    (fourPointTotalOddForcing (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
      (fun patch => patchCentroid motion time index patch)
      (quadrupoleCentroidForcing scales motion time index)).2

def referencePointShapeVelocity {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) : ℝ × ℝ :=
  shapeChartVelocity (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 /
      diagonalDifference motion time index) (unstableShape motion time index, stableShape motion time index) +
    referencePointShapeForcing scales motion time index

theorem FiniteMovingPatchFamily.centroid_regularized_shape_equation_of_prefix_safety {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) {scales : Scales} {horizon time : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (inside : time ∈ Icc 0 horizon)
    (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (differenceLower : ∀ current ∈ Icc 0 horizon,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference family.patchMotion current index)
    (imaginaryLower : ∀ current ∈ Icc 0 horizon, (1 / 16 : ℝ) ≤
      (negativeHalfDiagonal family.patchMotion current index / positiveHalfDiagonal family.patchMotion current index).im)
    (small : ∀ current ∈ Icc 0 horizon,
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index)).1| +
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index)).2| ≤ 1 / 4) :
    HasDerivWithinAt (fun current => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
      (referencePointShapeVelocity scales family.patchMotion time index) (Icc 0 horizon) time := by
  have safe (current : ℝ) (member : current ∈ Icc 0 horizon) :=
    reference_regularized_chart_imaginary_improvement scales family.patchMotion current index
      (differenceLower current member) (imaginaryLower current member) (small current member)
  have coherentSmall : |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
      (negativeHalfDiagonal family.patchMotion time index)).1| +
      |(pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
        (negativeHalfDiagonal family.patchMotion time index)).2| ≤ 1 / 4 := by
    rw [(safe time inside).2]
    exact small time inside
  have paper := pointShapeChart_eq_paper_shape_of_upper family.patchMotion time index
    (show 0 < (negativeHalfDiagonal family.patchMotion time index /
      positiveHalfDiagonal family.patchMotion time index).im by linarith [(imaginaryLower time inside)])
  have actual := family.centroid_coherent_shape_equation_of_reference_chart evolution inside index pathInside material coherentSmall
  dsimp only at actual
  rw [paper] at actual
  change HasDerivAt (fun current => pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
    (negativeHalfDiagonal family.patchMotion current index))
      (referencePointShapeVelocity scales family.patchMotion time index) time at actual
  apply actual.hasDerivWithinAt.congr_of_mem
  · intro current member
    exact (safe current member).2.symm
  · exact inside

end EulerNonuniqueness.Paper
