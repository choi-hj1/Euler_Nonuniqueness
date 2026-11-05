import EulerNonuniqueness.Section4.ReferenceContourShapeImprovement
import EulerNonuniqueness.Section4.ReferenceContourBoundaryImprovement

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_contour_monitor_improvement :
    ∃ monitor > 0, ∃ boundaryConstant ≥ (1 : ℝ),
    ∀ terminal shapeTolerance : ℝ, 0 ≤ terminal → 0 < shapeTolerance →
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
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < shapeTolerance) ∧
    (∀ current ∈ Icc 0 terminal, ∀ (index : Fin count) (patch : Fin 4),
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))) := by
  obtain ⟨shapeMonitor, shapeMonitorPositive, shapes⟩ := exists_uniform_reference_shape_improvement
  obtain ⟨boundaryMonitor, boundaryMonitorPositive, boundaryConstant, boundaryOne, boundaries⟩ :=
    exists_uniform_reference_boundary_improvement
  refine ⟨min shapeMonitor boundaryMonitor, lt_min shapeMonitorPositive boundaryMonitorPositive,
    boundaryConstant, boundaryOne, ?_⟩
  intro terminal shapeTolerance terminalNonnegative tolerancePositive
  obtain ⟨shapeRoot, shapeRootEight, shapeBounds⟩ := shapes terminal shapeTolerance terminalNonnegative tolerancePositive
  obtain ⟨boundaryRoot, boundaryRootEight, boundaryBounds⟩ := boundaries terminal terminalNonnegative
  refine ⟨max shapeRoot boundaryRoot, shapeRootEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal safe strictSafe geometry shapeSmall shapeMember
  constructor
  · exact shapeBounds scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity frequencyLarge ratioLarge
      alphaPositive strainSmall trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal
      safe strictSafe geometry (fun current inside label => (shapeSmall current inside label).trans_le (min_le_left _ _)) shapeMember
  · exact boundaryBounds scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity frequencyLarge ratioLarge
      alphaPositive strainSmall trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal
      safe strictSafe geometry (fun current inside label => (shapeSmall current inside label).trans_le (min_le_right _ _)) shapeMember

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
