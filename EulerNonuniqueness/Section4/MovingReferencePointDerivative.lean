import EulerNonuniqueness.Section4.ReferencePointRegularizedDerivative
import EulerNonuniqueness.Section4.MovingReferenceShootingCoordinates
import EulerNonuniqueness.Section3.MovingCentroidGaugeEuler

noncomputable section

open Set Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000

theorem movingReferenceShapeCoordinates_hasDerivAt_of_prefix_margin
    {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
    {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
    {initial : MovingContourState (count * 4)}
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial)
    (scales : Scales)
    (densityIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (radiusIdentity : ∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) =
      scales.radius (index.val + 1))
    (initialCircles : ∀ source, initial.2.2 source = standardCircleBanach)
    (marginPositive : 0 < margin) {time : ℝ} (timeNonnegative : 0 ≤ time) (beforeFinal : time < forwardHorizon)
    (safe : ∀ current ∈ Icc 0 time, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ)
    (index : Fin count)
    (differenceLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      diagonalDifference trajectory.movingFamily.patchMotion time index)
    (upper : 0 < (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index /
      positiveHalfDiagonal trajectory.movingFamily.patchMotion time index).im)
    (small : |unstableShape trajectory.movingFamily.patchMotion time index| +
      |stableShape trajectory.movingFamily.patchMotion time index| ≤ 1 / 4) :
    HasDerivAt (fun current => movingReferenceShapeCoordinates scales (trajectory.curve current) index)
      (referencePointShapeVelocity scales trajectory.movingFamily.patchMotion time index) time := by
  have inside : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨(neg_neg_of_pos trajectory.backward_positive).trans_le timeNonnegative, beforeFinal⟩
  have evolution := trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles marginPositive
    timeNonnegative beforeFinal safe
  have familyDensity : ∀ (source : Fin count) (patch : Fin 4), trajectory.movingFamily.density (finProdFinEquiv (source, patch)) =
      patchSign patch * scales.amplitude * scales.omega (source.val + 1) ^ 4 := densityIdentity
  have material (patch : Fin 4) (label : ℝ) :
      (trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales trajectory.movingFamily.patchMotion time)
          ((trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).boundary time label) := by
    rw [trajectory.movingFamily.patchVorticity_eq scales familyDensity]
    exact trajectory.movingFamily_material_equation_of_margin marginPositive inside (safe time ⟨timeNonnegative, le_rfl⟩) _ label
  have actual := trajectory.movingFamily.centroid_regularized_shape_hasDerivAt_of_point_safety evolution
    ⟨timeNonnegative, le_rfl⟩ index (fun _ => inside) material differenceLower upper small
  have agreement : (fun current => movingReferenceShapeCoordinates scales (trajectory.curve current) index) =ᶠ[𝓝 time]
      (fun current => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal trajectory.movingFamily.patchMotion current index)
        (negativeHalfDiagonal trajectory.movingFamily.patchMotion current index)) := by
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current currentInside
    dsimp only [movingReferenceShapeCoordinates]
    rw [← trajectory.patchCentroid_eq_curve_center initialCircles currentInside index 0,
      ← trajectory.patchCentroid_eq_curve_center initialCircles currentInside index 1,
      ← trajectory.patchCentroid_eq_curve_center initialCircles currentInside index 2,
      ← trajectory.patchCentroid_eq_curve_center initialCircles currentInside index 3]
    rfl
  exact actual.congr_of_eventuallyEq agreement

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
