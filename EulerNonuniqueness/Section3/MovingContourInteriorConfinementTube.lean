import EulerNonuniqueness.Section3.MovingContourInteriorMaterialNeighborhood

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

variable {count : ℕ} {configuration : FiniteContourConfiguration count}
  {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}

structure ContourInteriorConfinementTube
    (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
      backwardHorizon forwardHorizon initial)
    (terminal radius : ℝ) (distance weight mass : Fin count → ℝ) where
  beforeFinal : terminal < forwardHorizon
  safe : ∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
    (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ
  distancePositive : ∀ index, 0 < distance index
  weightNonnegative : ∀ index, 0 ≤ weight index
  massNonnegative : ∀ index, 0 ≤ mass index
  small : ∀ index, 192 * (trajectory.movingFamily.patch index).radius ≤ distance index
  inside : ∀ current ∈ Icc 0 terminal, ∀ source,
    current ∈ Ioo (trajectory.movingFamily.patch source).initialTime (trajectory.movingFamily.patch source).finalTime
  centerGaps : ∀ current ∈ Icc 0 terminal, ∀ index source, source ∈ Finset.univ.erase index →
    distance index + 3 * (trajectory.movingFamily.patch source).radius ≤
      ‖(trajectory.movingFamily.patch index).center current - (trajectory.movingFamily.patch source).center current‖
  weightBound : ∀ current ∈ Icc 0 terminal, ∀ index,
    (∫ position, inverseSquareVorticityWeight
      (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
      ((trajectory.movingFamily.patch index).center current) position) ≤ weight index
  shapeSmall : ∀ current ∈ Icc 0 terminal, ∀ index,
    ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < radius
  angularSmall : ∀ current ∈ Icc 0 terminal, ∀ index, ‖trajectory.contourAngular index current‖ < radius
  splitSmall : ∀ current ∈ Icc 0 terminal, ∀ index,
    ‖diskRelabelCurve (trajectory.contourAngular index current) 1 - standardCircleBanach‖ +
      ‖(trajectory.curve current).2.2 index - diskRelabelCurve (trajectory.contourAngular index current) 1‖ ≤ radius
  angularMember : ∀ current ∈ Icc 0 terminal, ∀ index,
    trajectory.contourAngular index current ∈ contourContinuousVectorSubmodule
  relativeMember : ∀ current ∈ Icc 0 terminal, ∀ index,
    (trajectory.curve current).2.2 index - diskRelabelCurve (trajectory.contourAngular index current) 1 ∈
      contourContinuousVectorSubmodule
  materialNear : ∀ current ∈ Ioo 0 terminal, ∀ index,
    Nonempty (ContourMaterialNeighborhood trajectory index current (distance index) (weight index) (mass index))

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
