import EulerNonuniqueness.Section4.ReferenceContourMonitorHorizonImprovement
import EulerNonuniqueness.Section4.ReferenceSafePrefixGeometry

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_mechanical_contour_improvement_on_horizon :
    ∃ monitor > 0, ∃ boundaryConstant ≥ (1 : ℝ),
    ∀ horizon shapeTolerance : ℝ, 0 ≤ horizon → 0 < shapeTolerance →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon → scales.amplitude = scaleRoot ^ 3 →
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
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference trajectory.movingFamily.patchMotion current index) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      diagonalDifference trajectory.movingFamily.patchMotion current index ≤ 2 * scales.length (index.val + 1) ^ 2) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      |radialShape trajectory.movingFamily.patchMotion current index| ≤ 1 / 2) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ ≤ scales.length (index.val + 1) / 64) →
    (∀ current ∈ Icc 0 terminal, ∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion current receiver -
          quadrupoleCenter trajectory.movingFamily.patchMotion current source‖) →
    (∀ current ∈ Icc 0 terminal, ∀ index, ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < monitor) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < shapeTolerance) ∧
    (∀ current ∈ Icc 0 terminal, ∀ (index : Fin count) (patch : Fin 4),
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))) := by
  obtain ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, improvements⟩ :=
    exists_uniform_reference_contour_monitor_improvement_on_horizon
  refine ⟨min monitor (1 / 48), lt_min monitorPositive (by norm_num), boundaryConstant, boundaryOne, ?_⟩
  intro horizon shapeTolerance horizonNonnegative tolerancePositive
  obtain ⟨rootMin, rootEight, improved⟩ := improvements horizon shapeTolerance horizonNonnegative tolerancePositive
  refine ⟨rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge terminal terminalNonnegative terminalBound amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe
    lengthSmall radiusSmall differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation shapeSmall shapeMember
  have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have boundary (current : ℝ) (inside : current ∈ Icc 0 terminal) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (1 / 16) := by
    apply trajectory.movingFamily.boundaryCloseToCircle_of_shape_norm scales current index patch (radiusIdentity index patch)
    · rw [trajectory.movingFamily.patchCentroid_eq]
      exact (trajectory.movingPatch_centroid_eq_center_of_initial_circles initialCircles
        ⟨by linarith [trajectory.backward_positive, inside.1], inside.2.trans_lt beforeFinal⟩ _).symm
    · exact (trajectory.movingPatch_phase_eq_density_time_of_margin initialClock marginPositive inside safe _).trans
        (by rw [densityIdentity])
    · have nearby := (shapeSmall current inside (finProdFinEquiv (index, patch))).trans_le (min_le_right _ _)
      change 3 * ‖(trajectory.curve current).2.2 (finProdFinEquiv (index, patch)) - standardCircleBanach‖ ≤ 1 / 16
      linarith
  have geometry := trajectory.reference_geometry_of_safe_prefix scales densityIdentity radiusIdentity initialCircles
    marginPositive terminalNonnegative beforeFinal safe amplitudePositive (zero_lt_one.trans_le frequencyLarge)
    (by linarith) lengthSmall radiusSmall differenceLower differenceUpper radialSmall asymmetrySmall centerSeparation boundary
  exact improved scales scaleRoot rootLarge terminal terminalNonnegative terminalBound amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe
    geometry (fun current inside label => (shapeSmall current inside label).trans_le (min_le_left _ _)) shapeMember

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

