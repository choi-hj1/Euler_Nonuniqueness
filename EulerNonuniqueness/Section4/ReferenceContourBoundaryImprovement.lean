import EulerNonuniqueness.Section4.ReferenceContourConfinement
import EulerNonuniqueness.Section3.MovingPaperSpectralBoundaryControl
import EulerNonuniqueness.Section3.MovingCentroidGaugeArea

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_actual_boundary_of_transverse_control :
    ∃ radius > 0, ∃ constant ≥ (1 : ℝ),
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial) (scales : Scales),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ horizon time : ℝ, time ∈ Icc 0 horizon → horizon < forwardHorizon →
    (∀ current ∈ Icc 0 horizon, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    ∀ (index : Fin count) (patch : Fin 4),
    ‖(trajectory.curve time).2.2 (finProdFinEquiv (index, patch)) - standardCircleBanach‖ < radius →
    ∀ bound : ℝ,
    constant * ‖diskPhysicalTransverseProjection
      (trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) time)‖ ≤ bound →
    BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch bound := by
  obtain ⟨radius, radiusPositive, constant, constantOne, boundary⟩ :=
    FiniteMovingPatchFamily.exists_boundaryCloseToCircle_of_area_spectral_coordinate
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  intro count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory scales
    densityIdentity radiusIdentity initialCircles initialClock marginPositive horizon time inside beforeFinal safe index patch
    nearby bound projected
  apply boundary trajectory.movingFamily scales time index patch (radiusIdentity index patch)
  · rw [trajectory.movingFamily.patchCentroid_eq]
    exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles
      ⟨by linarith [trajectory.backward_positive, inside.1], inside.2.trans_lt beforeFinal⟩ _).symm
  · exact (trajectory.movingPatch_phase_eq_density_time_of_margin initialClock marginPositive inside safe _).trans
      (by rw [densityIdentity])
  · exact nearby
  · exact trajectory.shape_area_eq_pi_of_margin initialCircles marginPositive inside beforeFinal safe _
  · exact projected

theorem exists_uniform_reference_boundary_improvement :
    ∃ monitor > 0, ∃ boundaryConstant ≥ (1 : ℝ), ∀ terminal : ℝ, 0 ≤ terminal →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha → scales.strain ≤ 1 →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {centerBound shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    terminal < forwardHorizon →
    (∀ current ∈ Icc 0 terminal, margin ≤ infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Ico 0 terminal, margin < infDist (trajectory.curve current)
      (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ReferenceCentroidFieldGeometry scales trajectory.movingFamily.patchMotion current index) →
    (∀ current ∈ Icc 0 terminal, ∀ index, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < monitor) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    ∀ current ∈ Icc 0 terminal, ∀ (index : Fin count) (patch : Fin 4),
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2)) := by
  obtain ⟨contourMonitor, contourMonitorPositive, contourConstant, contourConstantOne, confinements⟩ :=
    exists_uniform_reference_contour_confinement
  obtain ⟨boundaryRadius, boundaryPositive, boundaryConstant, boundaryOne, boundaries⟩ :=
    exists_uniform_actual_boundary_of_transverse_control
  refine ⟨min contourMonitor boundaryRadius, lt_min contourMonitorPositive boundaryPositive,
    boundaryConstant * (contourConstant + 1), by nlinarith, ?_⟩
  intro terminal terminalNonnegative
  obtain ⟨rootMin, rootEight, confined⟩ := confinements terminal terminalNonnegative
  refine ⟨rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe geometry shapeSmall shapeMember
  have actual := confined scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe geometry
    (fun current inside label => (shapeSmall current inside label).trans_le (min_le_left _ _)) shapeMember
  intro current inside index patch
  apply boundaries trajectory scales densityIdentity radiusIdentity initialCircles initialClock marginPositive terminal current
    inside beforeFinal safe index patch ((shapeSmall current inside _).trans_le (min_le_right _ _))
  have scalar := actual current inside index patch
  have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
  have frequencyPositive := scales.omega_pos (zero_lt_one.trans_le frequencyLarge) (by linarith) (index.val + 1)
  have denominator : 0 < scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2 := by positivity
  have positive : 0 ≤ (contourConstant + 1) / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) := by positivity
  have enlarged := scalar.le.trans (by linarith :
    (contourConstant + 1) / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2) / 8 ≤
      (contourConstant + 1) / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))
  have multiplied := mul_le_mul_of_nonneg_left enlarged (by linarith : 0 ≤ boundaryConstant)
  exact multiplied.trans_eq (by ring)

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
