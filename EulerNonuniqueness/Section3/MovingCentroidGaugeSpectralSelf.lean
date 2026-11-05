import EulerNonuniqueness.Section3.DiskPhysicalSpectralCoordinates
import EulerNonuniqueness.Section3.DiskSpectralSelfBounds
import EulerNonuniqueness.Section3.MovingCentroidGaugeArea

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd

namespace MovingCentroidGaugeTrajectory

theorem exists_uniform_physical_spectral_self_radius :
    ∃ radius > 0, ∃ remainderConstant ≥ 0, ∃ bilinearConstant ≥ 0,
    ∃ correctionConstant ≥ 0, ∃ neutralConstant ≥ 0,
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial),
      (∀ index, initial.2.2 index = standardCircleBanach) → 0 < margin →
      ∀ horizon time : ℝ, time ∈ Icc 0 horizon → horizon < forwardHorizon →
      (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
        (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
      ∀ index : Fin count, ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
      let coordinate := diskPhysicalSpectralCoordinate ((trajectory.curve time).2.2 index)
      diskStationaryChart (diskSpectralTubularChart coordinate) = (trajectory.curve time).2.2 index ∧
      diskSpectralTubularArea coordinate = Real.pi ∧
      ‖diskSpectralProjectedRemainder coordinate‖ ≤
        remainderConstant * ‖diskPhysicalTransverseProjection coordinate‖ ^ 3 ∧
      ‖diskSpectralFiberQuadraticBilinear coordinate‖ ≤ bilinearConstant ∧
      ‖diskSpectralMovingQuadraticCorrection coordinate‖ ≤ correctionConstant ∧
      (‖diskPhysicalTransverseProjection coordinate‖ ≤ 1 →
        ‖diskRelabelNeutralCLM (diskSpectralTubularEulerField coordinate)‖ ≤
          neutralConstant * ‖diskPhysicalTransverseProjection coordinate‖ ^ 2) := by
  obtain ⟨tubeRadius, tubePositive, remainderConstant, remainderNonnegative,
    bilinearConstant, bilinearNonnegative, correctionConstant, correctionNonnegative,
    neutralConstant, neutralNonnegative, selfBounds⟩ :=
    diskSpectral_exists_uniform_projected_self_bounds
  obtain ⟨radius, radiusPositive, coordinateBounds⟩ :=
    diskPhysicalSpectralCoordinate_exists_radius tubePositive
  refine ⟨radius, radiusPositive, remainderConstant, remainderNonnegative,
    bilinearConstant, bilinearNonnegative, correctionConstant, correctionNonnegative,
    neutralConstant, neutralNonnegative, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory initialCircles marginPositive horizon time inside beforeFinal safe index near
  obtain ⟨rightInverse, areaIdentity, tubeBound, _continuousVector⟩ :=
    coordinateBounds ((trajectory.curve time).2.2 index) near
  have area : diskSpectralTubularArea
      (diskPhysicalSpectralCoordinate ((trajectory.curve time).2.2 index)) = Real.pi :=
    areaIdentity.trans (trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive
      inside beforeFinal safe index)
  exact ⟨rightInverse, area, selfBounds _ tubeBound.le area⟩

end MovingCentroidGaugeTrajectory

end EulerNonuniqueness.Paper
