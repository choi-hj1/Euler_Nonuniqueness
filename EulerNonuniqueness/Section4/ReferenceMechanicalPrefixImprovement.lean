import EulerNonuniqueness.Section4.ReferenceMonitoredNeutralSafety
import EulerNonuniqueness.Section4.ReferenceMonitoredDiagonalSafety
import EulerNonuniqueness.Section4.ReferenceMonitoredCenterSafety
import EulerNonuniqueness.Section4.ReferenceMonitoredClearanceSafety
import EulerNonuniqueness.Section4.ReferenceMonitoredSaddleSafety

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_geometric_monitor_improvement :
    ∃ memory ≥ (1 : ℝ), ∃ diagonalConstant ≥ (0 : ℝ), ∃ internal ≥ (0 : ℝ),
    ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
    ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
    ∀ {count : ℕ}, 0 < count → ∀ {configuration : FiniteContourConfiguration (count * 4)}
      {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin backwardHorizon forwardHorizon initial)
      (scales : Scales),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ label, initial.2.2 label = standardCircleBanach) → initial.1 = 0 →
    0 < shapeRadius → 0 < margin → margin ≤ shapeRadius / 8 → margin ≤ 1 / 8 →
    (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second) →
    ∀ {terminal shapeStop threshold bound tolerance : ℝ}, 0 < terminal → terminal ≤ 2 → terminal < forwardHorizon →
    0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
    shapeStop ≤ 1 / 48 → shapeStop ≤ shapeRadius / 2 → 0 ≤ bound → 0 ≤ tolerance →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) * (1 + (1 : ℝ) / 16) ≤ scales.length (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤ 1) →
    (∀ index : Fin count, scales.omega (index.val + 1) * scales.length (index.val + 1) ≤
      tolerance * scales.location (index.val + 1)) →
    ∀ {phase unstable : Fin count → ℝ},
    ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
    (∀ index, |unstable index| ≤ radius) →
    (∀ current ∈ Icc 0 terminal, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).1| ≤ radius) →
    (∀ label, ‖(trajectory.curve terminal).2.2 label - standardCircleBanach‖ < shapeStop) →
    (∀ current ∈ Icc 0 terminal, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (bound / scales.omega (index.val + 1) ^ 2)) →
    (∀ index : Fin count, bound / scales.omega (index.val + 1) ^ 2 ≤ 1 / 16) →
    scales.strain ≤ 1 → scales.hessian ≤ 1 →
    (∀ index : Fin count, memory * scales.hessian * scales.length (index.val + 1) < 1 / 128) →
    (∀ index : Fin count, scales.length (index.val + 1) < momentRadius / (8 * (memory + 1))) →
    (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
      scales.omega (index.val + 1) * radius / 16) →
    (2 * diagonalConstant * (scales.strain + scales.hessian) +
      48 * bound ^ 2 / (scales.amplitude * scales.frequency ^ 7) ≤ 1 / 4) →
    (2 * ((15120 / Real.pi) * scales.strain + 1800 * tolerance) ≤ 1 / 4) →
    (2 * (600 * tolerance + (3456 / Real.pi) * scales.strain +
      (48 / Real.pi) * ∑' source : ℕ, scales.circulation (source + 1) / scales.location (source + 1)) ≤ 1 / 2) →
    ∀ monitor, referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve terminal) monitor < 0 := by
  obtain ⟨memory, memoryOne, neutralImprovements⟩ := exists_uniform_reference_monitored_neutral_improvement
  obtain ⟨diagonalConstant, diagonalNonnegative, diagonalImprovements⟩ := exists_uniform_reference_monitored_diagonal_improvement
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive,
    maximumSmall, saddleImprovements⟩ := exists_uniform_reference_monitored_saddle_improvement
  refine ⟨memory, memoryOne, diagonalConstant, diagonalNonnegative, internal, internalNonnegative,
    momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count countPositive configuration shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory scales densityIdentity radiusIdentity initialCircles initialClock shapePositive marginPositive marginShape marginUnit marginSlack
    terminal shapeStop threshold bound tolerance terminalPositive terminalBound beforeFinal amplitudePositive frequencyLarge ratioLarge
    alphaPositive stopSmall stopShape boundNonnegative toleranceNonnegative lengthSmall strongRadiusSmall omegaLength
    relativeOmegaLength phase unstable initialDisks thresholdSmall initialBound closed unstableBound shapeImprovement boundary
    deformationSmall strainSmall hessianSmall neutralSmall momentSmall forcingSmall diagonalBudget pairBudget absoluteBudget
  have radiusSmall (index : Fin count) : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000 := by
    have positive := scales.radius_pos amplitudePositive (zero_lt_one.trans_le frequencyLarge) (by linarith) (index.val + 1)
    linarith [strongRadiusSmall index]
  have neutral := neutralImprovements trajectory scales densityIdentity radiusIdentity initialCircles initialClock marginPositive
    terminalPositive terminalBound beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall lengthSmall radiusSmall
    initialDisks closed strainSmall hessianSmall neutralSmall
  have diagonal := diagonalImprovements trajectory scales densityIdentity radiusIdentity initialCircles initialClock marginPositive
    terminalPositive terminalBound beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall boundNonnegative
    lengthSmall strongRadiusSmall omegaLength initialDisks thresholdSmall closed boundary deformationSmall strainSmall hessianSmall diagonalBudget
  have centers := trajectory.reference_center_monitors_strict_of_nonpositive_prefix scales densityIdentity radiusIdentity initialCircles
    initialClock marginPositive terminalPositive.le terminalBound beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall
    initialDisks lengthSmall strongRadiusSmall toleranceNonnegative relativeOmegaLength pairBudget absoluteBudget closed
  have saddles := saddleImprovements radius radiusPositive radiusBound trajectory scales densityIdentity radiusIdentity initialCircles
    initialClock marginPositive terminalPositive.le beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall
    (by linarith : 0 ≤ memory) boundNonnegative hessianSmall lengthSmall radiusSmall initialDisks thresholdSmall initialBound closed
    boundary deformationSmall (fun current member index => (neutral current member index).2.1) momentSmall unstableBound forcingSmall
  have currentInside : terminal ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive], beforeFinal⟩
  have terminalMember : terminal ∈ Icc 0 terminal := ⟨terminalPositive.le, le_rfl⟩
  intro monitor
  cases monitor with
  | clearance =>
      exact trajectory.reference_clearance_monitor_strict_of_nonpositive_monitors countPositive scales radiusIdentity
        initialCircles shapePositive marginPositive marginShape marginUnit marginSlack currentInside stopShape lengthSmall radiusSmall
        (closed terminal terminalMember)
  | shape label => exact sub_neg.mpr (shapeImprovement label)
  | diagonal index =>
      have geometric := trajectory.movingReferenceGeometricObservables_eq_paper initialCircles currentInside index
      have improved := diagonal terminal terminalMember index
      rw [← geometric.1] at improved
      change |movingReferenceDiagonalDifference (trajectory.curve terminal) index / scales.length (index.val + 1) ^ 2 - 1| - 1 / 2 < 0
      linarith
  | asymmetry index =>
      have geometric := trajectory.movingReferenceGeometricObservables_eq_paper initialCircles currentInside index
      have improved := (neutral terminal terminalMember index).2.2
      rw [← geometric.2.1] at improved
      have divided : ‖movingReferenceAsymmetry (trajectory.curve terminal) index‖ / scales.length (index.val + 1) < 1 / 128 :=
        (div_lt_iff₀ (scales.length_pos _)).mpr (by linarith)
      change ‖movingReferenceAsymmetry (trajectory.curve terminal) index‖ / scales.length (index.val + 1) - 1 / 64 < 0
      linarith
  | radial index => exact (saddles terminal terminalMember index).2.1
  | branch index => exact (saddles terminal terminalMember index).2.2
  | pair receiver source => exact centers.1 terminal terminalMember receiver source
  | center label => exact centers.2 terminal terminalMember label

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
