import EulerNonuniqueness.Section4.ReferenceMechanicalMonitorBounds
import EulerNonuniqueness.Section4.ReferenceMechanicalContourImprovement

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
  {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
  {initial : MovingContourState (count * 4)}

theorem reference_paper_geometry_of_nonpositive_monitors
    (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
      backwardHorizon forwardHorizon initial) (scales : Scales)
    (initialCircles : ∀ label, initial.2.2 label = standardCircleBanach)
    {time shapeStop : ℝ} (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon)
    (bounds : ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop
      (trajectory.curve time) monitor ≤ 0) :
    (margin ≤ infDist (trajectory.curve time) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ) ∧
    (∀ index : Fin count,
      scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference trajectory.movingFamily.patchMotion time index ∧
      diagonalDifference trajectory.movingFamily.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2 ∧
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion time index‖ ≤ scales.length (index.val + 1) / 64 ∧
      |radialShape trajectory.movingFamily.patchMotion time index| ≤ 1 / 2 ∧
      1 / 16 ≤ (negativeHalfDiagonal trajectory.movingFamily.patchMotion time index /
        positiveHalfDiagonal trajectory.movingFamily.patchMotion time index).im) ∧
    (∀ receiver source : Fin count, receiver ≠ source →
      |scales.location (receiver.val + 1) - scales.location (source.val + 1)| / 2 ≤
        ‖quadrupoleCenter trajectory.movingFamily.patchMotion time receiver -
          quadrupoleCenter trajectory.movingFamily.patchMotion time source‖ ∧
      ‖quadrupoleCenter trajectory.movingFamily.patchMotion time receiver -
          quadrupoleCenter trajectory.movingFamily.patchMotion time source‖ ≤
        2 * |scales.location (receiver.val + 1) - scales.location (source.val + 1)|) := by
  have geometric (index : Fin count) := trajectory.movingReferenceGeometricObservables_eq_paper initialCircles inside index
  refine ⟨referenceMechanicalMonitor_clearance (bounds .clearance), ?_, ?_⟩
  · intro index
    have diagonal := referenceMechanicalMonitor_diagonal index (bounds (.diagonal index))
    rw [(geometric index).1] at diagonal
    have asymmetry := referenceMechanicalMonitor_asymmetry index (bounds (.asymmetry index))
    rw [(geometric index).2.1] at asymmetry
    have regularized := trajectory.movingReferenceMechanicalObservables_eq_paper initialCircles scales inside index diagonal.1
    have radial := referenceMechanicalMonitor_radial index (bounds (.radial index))
    rw [regularized.1] at radial
    have branch := referenceMechanicalMonitor_branch index (bounds (.branch index))
    rw [regularized.2] at branch
    exact ⟨diagonal.1, diagonal.2, asymmetry, radial, branch⟩
  · intro receiver source different
    have pair := referenceMechanicalMonitor_pair receiver source different (bounds (.pair receiver source))
    rwa [(geometric receiver).2.2, (geometric source).2.2] at pair

theorem exists_uniform_reference_monitored_contour_improvement :
    ∃ monitor > 0, ∃ boundaryConstant ≥ (1 : ℝ),
    ∀ terminal shapeTolerance : ℝ, 0 ≤ terminal → 0 < shapeTolerance →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha → scales.strain ≤ 1 →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ}
      {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ index, initial.2.2 index = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    terminal < forwardHorizon →
    ∀ shapeStop : ℝ, shapeStop < monitor →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) index ≤ 0) →
    (∀ current ∈ Ico 0 terminal, ∀ index,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) index < 0) →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
    (∀ current ∈ Icc 0 terminal, ∀ index, (trajectory.curve current).2.2 index ∈ contourContinuousVectorSubmodule) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ‖(trajectory.curve current).2.2 index - standardCircleBanach‖ < shapeTolerance) ∧
    (∀ current ∈ Icc 0 terminal, ∀ (index : Fin count) (patch : Fin 4),
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2))) := by
  obtain ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, improvements⟩ :=
    exists_uniform_reference_mechanical_contour_improvement
  refine ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, ?_⟩
  intro terminal shapeTolerance terminalNonnegative tolerancePositive
  obtain ⟨rootMin, rootEight, improved⟩ := improvements terminal shapeTolerance terminalNonnegative tolerancePositive
  refine ⟨rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count configuration shapeRadius gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal shapeStop stopSmall
    closed strict lengthSmall radiusSmall shapeMember
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  have geometry (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (closed current member)
  apply improved scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive beforeFinal
  · intro current member
    exact (geometry current member).1
  · intro current member
    exact referenceMechanicalMonitor_strict_clearance (strict current member .clearance)
  · exact lengthSmall
  · exact radiusSmall
  · intro current member index
    exact ((geometry current member).2.1 index).1
  · intro current member index
    exact ((geometry current member).2.1 index).2.1
  · intro current member index
    exact ((geometry current member).2.1 index).2.2.2.1
  · intro current member index
    exact ((geometry current member).2.1 index).2.2.1
  · intro current member receiver source different
    exact ((geometry current member).2.2 receiver source different).1
  · intro current member label
    exact (referenceMechanicalMonitor_shape label (closed current member (.shape label))).trans_lt stopSmall
  · exact shapeMember

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
