import EulerNonuniqueness.Section6.MovingMaterialShapeDynamics
import EulerNonuniqueness.Section6.PaperShapeTubeBranch

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem centroid_paper_shape_equation {count : ℕ} (family : FiniteMovingPatchFamily (count * 4))
    {scales : Scales} {horizon time : ℝ} (evolution : FinitePatchEvolution scales family.patchMotion horizon)
    (inside : time ∈ Ioo 0 horizon) (index : Fin count)
    (pathInside : ∀ patch : Fin 4, time ∈ Ioo (family.patch (finProdFinEquiv (index, patch))).initialTime
      (family.patch (finProdFinEquiv (index, patch))).finalTime)
    (material : ∀ patch label, (family.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
      biotSavart (Paper.patchVorticity scales family.patchMotion time)
        ((family.patch (finProdFinEquiv (index, patch))).boundary time label))
    (positiveContinuous : ContinuousOn (fun current => positiveHalfDiagonal family.patchMotion current index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun current => negativeHalfDiagonal family.patchMotion current index) (Icc 0 horizon))
    (positiveNonzero : ∀ current ∈ Icc 0 horizon, positiveHalfDiagonal family.patchMotion current index ≠ 0)
    (negativeNonzero : ∀ current ∈ Icc 0 horizon, negativeHalfDiagonal family.patchMotion current index ≠ 0)
    (initialUpper : 0 < (negativeHalfDiagonal family.patchMotion 0 index /
      positiveHalfDiagonal family.patchMotion 0 index).im)
    (small : ∀ current ∈ Icc 0 horizon,
      |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
        (negativeHalfDiagonal family.patchMotion current index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion current index)
        (negativeHalfDiagonal family.patchMotion current index)).2| ≤ 1 / 4)
    (noncollision : Section6.FourPointNoncollision (Section6.centrallySymmetricFourPoint
      (positiveHalfDiagonal family.patchMotion time index) (negativeHalfDiagonal family.patchMotion time index)))
    (normOrder : ‖negativeHalfDiagonal family.patchMotion time index‖ <
      ‖positiveHalfDiagonal family.patchMotion time index‖) :
    let positions := fun patch => patchCentroid family.patchMotion time index patch
    let coefficient := scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2
    let forcing := quadrupoleCentroidForcing scales family.patchMotion time index
    HasDerivAt (fun current => (unstableShape family.patchMotion current index,
        stableShape family.patchMotion current index))
      (Section6.shapeChartVelocity (coefficient / diagonalDifference family.patchMotion time index)
          (unstableShape family.patchMotion time index, stableShape family.patchMotion time index) +
        Section6.pointShapeForcing (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index)
          (Section6.fourPointTotalOddForcing coefficient positions forcing).1
          (Section6.fourPointTotalOddForcing coefficient positions forcing).2) time := by
  have closedInside : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have agrees := paper_shape_eq_coherent_chart_on_small_interval family.patchMotion index
    positiveContinuous negativeContinuous positiveNonzero negativeNonzero initialUpper small
  have derivative := family.centroid_coherent_shape_equation_of_small evolution closedInside index
    pathInside material noncollision normOrder (small time closedInside)
  change HasDerivAt (fun current => Section6.pointShapeChart
      (positiveHalfDiagonal family.patchMotion current index) (negativeHalfDiagonal family.patchMotion current index))
    (Section6.shapeChartVelocity
        ((scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) /
          diagonalDifference family.patchMotion time index)
        (Section6.pointShapeChart (positiveHalfDiagonal family.patchMotion time index)
          (negativeHalfDiagonal family.patchMotion time index)) + _) time at derivative
  rw [agrees time closedInside] at derivative
  apply derivative.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds inside.1 inside.2] with current currentInside
  exact (agrees current currentInside).symm

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
