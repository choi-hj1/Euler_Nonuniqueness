import EulerNonuniqueness.Section4.ReferenceMonitoredMaterialPrefix
import EulerNonuniqueness.Section4.ReferenceMonitoredShapeSafety
import EulerNonuniqueness.Section4.ReferenceUnclampedShapeBarrier

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_monitored_saddle_improvement :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
    ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
    ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
      {shapeRadius gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin backwardHorizon forwardHorizon initial)
      (scales : Scales),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ label, initial.2.2 label = standardCircleBanach) → initial.1 = 0 → 0 < margin →
    ∀ {terminal shapeStop threshold memory bound : ℝ}, 0 ≤ terminal → terminal < forwardHorizon →
    0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
    shapeStop ≤ 1 / 48 → 0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000) →
    ∀ {phase unstable : Fin count → ℝ},
    ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable threshold → threshold ≤ 1 / 2 →
    (∀ index, |unstable index| ≤ radius) →
    (∀ current ∈ Icc 0 terminal, ∀ monitor,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) monitor ≤ 0) →
    (∀ current ∈ Icc 0 terminal, ∀ index patch,
      BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion current index patch (bound / scales.omega (index.val + 1) ^ 2)) →
    (∀ index : Fin count, bound / scales.omega (index.val + 1) ^ 2 ≤ 1 / 16) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      ‖centroidAsymmetry trajectory.movingFamily.patchMotion current index‖ ≤ memory * scales.length (index.val + 1) ^ 2) →
    (∀ index : Fin count, scales.length (index.val + 1) < momentRadius / (8 * (memory + 1))) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).1| ≤ radius) →
    (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
      scales.omega (index.val + 1) * radius / 16) →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).2| < radius ∧
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) (.radial index) < 0 ∧
      referenceMechanicalMonitor configuration scales shapeRadius gap margin shapeStop (trajectory.curve current) (.branch index) < 0 := by
  obtain ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive,
    maximumSmall, barrier⟩ := FiniteMovingPatchFamily.exists_uniform_unclamped_reference_shape_barrier
  refine ⟨internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound count configuration shapeRadius gap margin backwardHorizon forwardHorizon initial
    trajectory scales densityIdentity radiusIdentity initialCircles initialClock marginPositive terminal shapeStop threshold memory bound
    terminalNonnegative beforeFinal amplitudePositive frequencyLarge ratioLarge alphaPositive stopSmall memoryNonnegative boundNonnegative
    hessianSmall lengthSmall radiusSmall phase unstable initialDisks thresholdSmall initialBound closed boundary deformationSmall
    momentBound momentSmall unstableBound forcingSmall
  obtain ⟨evolution, geometry, _, material⟩ := trajectory.reference_material_data_of_nonpositive_monitors scales
    densityIdentity radiusIdentity initialCircles initialClock marginPositive terminalNonnegative beforeFinal amplitudePositive
    (zero_lt_one.trans_le frequencyLarge) (by linarith) stopSmall lengthSmall radiusSmall closed
  have inside (current : ℝ) (member : current ∈ Icc 0 terminal) :
      current ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, member.1], member.2.trans_lt beforeFinal⟩
  have decoded (current : ℝ) (member : current ∈ Icc 0 terminal) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (closed current member)
  have coordinateIdentity (current : ℝ) (member : current ∈ Icc 0 terminal) (index : Fin count) :
      movingReferenceShapeCoordinates scales (trajectory.curve current) index =
        regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal trajectory.movingFamily.patchMotion current index)
          (negativeHalfDiagonal trajectory.movingFamily.patchMotion current index) := by
    dsimp only [movingReferenceShapeCoordinates]
    rw [← trajectory.patchCentroid_eq_curve_center initialCircles (inside current member) index 0,
      ← trajectory.patchCentroid_eq_curve_center initialCircles (inside current member) index 1,
      ← trajectory.patchCentroid_eq_curve_center initialCircles (inside current member) index 2,
      ← trajectory.patchCentroid_eq_curve_center initialCircles (inside current member) index 3]
    rfl
  have actual := barrier radius radiusPositive radiusBound trajectory.movingFamily evolution terminalNonnegative
    amplitudePositive frequencyLarge ratioLarge alphaPositive memoryNonnegative boundNonnegative hessianSmall initialDisks
    thresholdSmall initialBound geometry (fun current member _ => inside current member)
    (by
      intro current member source label
      rw [trajectory.movingFamily.patchVorticity_eq scales densityIdentity]
      exact material current member source label)
    (fun _ index => bound / scales.omega (index.val + 1) ^ 2) boundary
    (fun _ _ _ => div_nonneg boundNonnegative (sq_nonneg _)) (fun _ _ index => deformationSmall index)
    (fun _ _ _ => le_rfl)
    (fun index => (lengthSmall index).trans (by linarith [scales.location_le_one (index.val + 1)]))
    (fun current member index => ((decoded current member).2.1 index).1)
    (fun current member index => ((decoded current member).2.1 index).2.1) momentBound momentSmall
    (by
      intro current member index
      simpa only [coordinateIdentity current member index] using unstableBound current member index)
    forcingSmall
  intro current member index
  have agreement := (coordinateIdentity current member index).trans (actual current member index).2.1
  have stableBound : |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).2| < radius := by
    simpa only [agreement] using (actual current member index).2.2.2
  exact ⟨stableBound, reference_radial_branch_monitors_strict_of_coordinate_box scales (trajectory.curve current) index
    (radiusBound.trans maximumSmall) (unstableBound current member index) stableBound.le
    (closed current member (.diagonal index)) (closed current member (.branch index))⟩

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
