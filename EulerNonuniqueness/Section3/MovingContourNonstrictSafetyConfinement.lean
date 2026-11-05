import EulerNonuniqueness.Section3.MovingContourQuarticInteriorConfinement
import EulerNonuniqueness.Section3.ContourConfinementShapeMonitor
import EulerNonuniqueness.Section3.MovingContourMaterialNeighborhood

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

open EulerNonuniqueness.Section6

theorem exists_uniform_nonstrict_safety_contour_confinement_on_horizon :
    ∃ monitor > 0, ∀ forcingConstant horizon : ℝ, 0 ≤ forcingConstant → 0 ≤ horizon →
    ∃ rootMin ≥ (8 : ℝ), ∀ scaleRoot : ℝ, rootMin ≤ scaleRoot →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration count}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState count}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ (frequency distance weight mass : Fin count → ℝ),
    (∀ index, 1 ≤ frequency index) →
    (∀ index, |configuration.density index| = scaleRoot ^ 3 * frequency index ^ 4) →
    (∀ index, weight index ≤ forcingConstant * frequency index) →
    (∀ index, (trajectory.movingFamily.patch index).radius / distance index ≤
      forcingConstant / (scaleRoot * frequency index)) →
    (∀ index, weight index ^ 2 + mass index * weight index / distance index ^ 2 ≤
      forcingConstant * frequency index ^ 2) → terminal < forwardHorizon →
    (∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ index, 0 < distance index) → (∀ index, 0 ≤ weight index) → (∀ index, 0 ≤ mass index) →
    (∀ index, 192 * (trajectory.movingFamily.patch index).radius ≤ distance index) →
    (∀ current ∈ Icc 0 terminal, ∀ index source, source ∈ Finset.univ.erase index →
      distance index + 3 * (trajectory.movingFamily.patch source).radius ≤
        ‖(trajectory.movingFamily.patch index).center current - (trajectory.movingFamily.patch source).center current‖) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
        ((trajectory.movingFamily.patch index).center current) position) ≤ weight index) →
    (∀ base ∈ Ioo 0 terminal, ∀ index, ∀ᶠ current in 𝓝 base,
      (∀ source ∈ Finset.univ.erase index, distance index + 3 * (trajectory.movingFamily.patch source).radius ≤
        ‖(trajectory.movingFamily.patch index).center current - (trajectory.movingFamily.patch source).center current‖) ∧
      (∫ position, inverseSquareVorticityWeight
        (trajectory.movingFamily.subfamilyVorticity (Finset.univ.erase index) current)
        ((trajectory.movingFamily.patch index).center current) position) ≤ weight index ∧
      (∫ position, |trajectory.movingFamily.patchVorticity current index position|) ≤ mass index) →
    (∀ current ∈ Icc 0 terminal, ∀ index, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < monitor) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      ‖diskPhysicalTransverseProjection (trajectory.spectralCoordinate index current)‖ <
        ((forcingConstant + 1) / (scaleRoot ^ 2 * frequency index ^ 2)) / 8 := by
  obtain ⟨radius, radiusPositive, confinements⟩ := exists_uniform_actual_quartic_contour_interior_confinement_on_horizon
  obtain ⟨monitor, monitorPositive, monitorLe, monitors⟩ := exists_contour_confinement_shape_monitor_radius radiusPositive
  refine ⟨monitor, monitorPositive, ?_⟩
  intro forcingConstant horizon forcingNonnegative horizonNonnegative
  obtain ⟨rootMin, rootEight, confined⟩ := confinements forcingConstant horizon forcingNonnegative horizonNonnegative
  refine ⟨rootMin, rootEight, ?_⟩
  intro scaleRoot rootLarge terminal terminalNonnegative terminalBound count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon
    initial trajectory initialCircles initialClock marginPositive frequency distance weight mass frequencyLarge densityMagnitude
    weightScale ratioScale numeratorScale beforeFinal safe distancePositive weightNonnegative massNonnegative
    small centerGaps weightBounds geometryNear shapeSmall shapeMember
  have globalInside (current : ℝ) (inside : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [inside.1, trajectory.backward_positive], inside.2.trans_lt beforeFinal⟩
  have analytic (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) :=
    monitors ((trajectory.curve current).2.2 index) (shapeSmall current inside index) (shapeMember current inside index)
  have tube : ContourInteriorConfinementTube trajectory terminal radius distance weight mass := {
    beforeFinal := beforeFinal
    safe := safe
    distancePositive := distancePositive
    weightNonnegative := weightNonnegative
    massNonnegative := massNonnegative
    small := small
    inside := fun current inside source => globalInside current inside
    centerGaps := centerGaps
    weightBound := weightBounds
    shapeSmall := fun current inside index => (shapeSmall current inside index).trans_le monitorLe
    angularSmall := fun current inside index => (analytic current inside index).1
    splitSmall := fun current inside index => (analytic current inside index).2.1
    angularMember := fun current inside index => (analytic current inside index).2.2.1
    relativeMember := fun current inside index => (analytic current inside index).2.2.2
    materialNear := fun base inside index => trajectory.exists_materialNeighborhood_of_interior_nonstrict_margin initialCircles
      marginPositive index inside beforeFinal safe (geometryNear base inside index) }
  exact confined scaleRoot rootLarge terminal terminalNonnegative terminalBound trajectory initialCircles initialClock marginPositive frequency distance weight mass
    frequencyLarge densityMagnitude weightScale ratioScale numeratorScale tube

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
