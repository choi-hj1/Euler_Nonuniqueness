import EulerNonuniqueness.Section3.CanonicalExteriorPrefixRecovery
import EulerNonuniqueness.Section3.MovingContourConfinementTube
import EulerNonuniqueness.Section3.MovingCentroidGaugeContourRate
import EulerNonuniqueness.Section3.MovingCentroidGaugeContourRateModel
import EulerNonuniqueness.Section3.MovingCentroidGaugeAngularCost
import EulerNonuniqueness.General.ContourRateBudget
import EulerNonuniqueness.Section3.CanonicalExteriorAffineMovingSlope
import EulerNonuniqueness.Section3.MovingCanonicalShapeEquation

noncomputable section

open Set Metric MeasureTheory Filter
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

open EulerNonuniqueness.Section6

theorem exists_uniform_named_contour_prefix_slope_radius :
    ∃ radius > 0, ∃ constant ≥ 1,
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ horizon time distance weight mass control : ℝ,
    time ∈ Icc 0 horizon → horizon < forwardHorizon →
    (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    ∀ (index : Fin count) (positive : 0 < distance), 0 ≤ weight → 0 ≤ mass →
    configuration.density index ≠ 0 → 192 * (trajectory.movingFamily.patch index).radius ≤ distance →
    (∀ source ∈ Finset.univ.erase index, ∀ position ∈ (trajectory.movingFamily.patch source).domain time,
      distance ≤ ‖(trajectory.movingFamily.patch index).center time - position‖) →
    (∫ position, inverseSquareVorticityWeight
      (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) time)
      ((trajectory.movingFamily.patch index).center time) position) ≤ weight →
    ‖(trajectory.curve time).2.2 index - standardCircleBanach‖ < radius →
    ‖diskNeutralCLM (trajectory.spectralCoordinate index time)‖ ≤ radius →
    ‖diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1 - standardCircleBanach‖ +
      ‖(trajectory.curve time).2.2 index - diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1‖ ≤ radius →
    weight / |configuration.density index| ≤ radius →
    contourAreaFunctional ((trajectory.curve time).2.2 index) = Real.pi →
    contourCentroidFunctional ((trajectory.curve time).2.2 index) = 0 →
    ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index time)‖ ≤ control →
    weight / |configuration.density index| ≤ control → control ≤ 1 →
    ∀ left right : ℝ, time ∈ Ioo left right →
    (∀ current ∈ Ioo left right, ∀ source,
      current ∈ Ioo (trajectory.movingFamily.patch source).initialTime (trajectory.movingFamily.patch source).finalTime) →
    (∀ current ∈ Ioo left right, ∀ source label,
      (trajectory.movingFamily.patch source).boundaryVelocity current label =
        biotSavart (trajectory.movingFamily.vorticity current) ((trajectory.movingFamily.patch source).boundary current label)) →
    (∀ current ∈ Ioo left right, (trajectory.movingFamily.patch index).center =ᶠ[nhds current]
      (trajectory.movingFamily.patch index).centroid) →
    (∀ current ∈ Ioo left right, ∀ source ∈ Finset.univ.erase index,
      distance + 3 * (trajectory.movingFamily.patch source).radius ≤
        ‖(trajectory.movingFamily.patch index).center current - (trajectory.movingFamily.patch source).center current‖) →
    (∀ current ∈ Ioo left right, (∫ position, inverseSquareVorticityWeight
      (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
      ((trajectory.movingFamily.patch index).center current) position) ≤ weight) →
    (∀ current ∈ Ioo left right, (∫ position, |trajectory.movingFamily.patchVorticity current index position|) ≤ mass) →
    diskNeutralCLM (trajectory.spectralCoordinate index time) ∈ contourContinuousVectorSubmodule →
    (trajectory.curve time).2.2 index - diskRelabelCurve
      (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1 ∈ contourContinuousVectorSubmodule →
    contourCentroidFunctional ((trajectory.curve time).2.2 index) =
      contourCentroidFunctional (diskRelabelCurve (diskNeutralCLM (trajectory.spectralCoordinate index time)) 1) →
    ∀ threshold : ℝ,
      constant * (|configuration.density index| * control ^ 3 + weight * control ^ 2 +
        weight * ((trajectory.movingFamily.patch index).radius / distance) * control +
        (weight ^ 2 + mass * weight / distance ^ 2) / |configuration.density index|) < threshold →
      ∀ᶠ later in 𝓝[>] time,
        slope (fun current => ‖trajectory.contourInteraction index current‖) time later < threshold := by
  unfold contourInteraction contourAngular
  with_reducible_and_instances
    exact exists_uniform_actual_contour_prefix_slope_radius

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

