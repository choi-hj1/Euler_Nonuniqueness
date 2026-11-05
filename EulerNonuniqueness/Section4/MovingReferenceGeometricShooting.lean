import EulerNonuniqueness.Section4.MovingReferenceStoppedShooting
import EulerNonuniqueness.Section4.ReferenceUnclampedShapeBarrier

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem referenceShapeForcingBudget_mono_internal (scales : Scales) (index : ℕ)
    {first second memory bound : ℝ} (ordered : first ≤ second) (strainNonnegative : 0 ≤ scales.strain) :
    referenceShapeForcingBudget scales index first memory bound ≤ referenceShapeForcingBudget scales index second memory bound := by
  dsimp only [referenceShapeForcingBudget]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_right _ strainNonnegative
  apply div_le_div_of_nonneg_right _ Real.pi_pos.le
  have multiplied := mul_le_mul_of_nonneg_right ordered (sq_nonneg memory)
  nlinarith only [multiplied]

theorem exists_uniform_geometric_reference_shooting :
    ∃ internal ≥ (0 : ℝ), ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
      ∀ {count : ℕ} {configuration : FiniteContourConfiguration (count * 4)}
        {centerBound shapeRadius gap margin backwardHorizon forwardHorizon horizon : ℝ},
      ∀ (scales : Scales) (phase : Fin count → ℝ)
        (initial : closedBall (0 : Fin count → ℝ) radius → MovingContourState (count * 4))
        (trajectories : ∀ parameter, MovingCentroidGaugeTrajectory configuration centerBound shapeRadius gap margin
          backwardHorizon forwardHorizon (initial parameter)),
      (∀ (index : Fin count) (patch : Fin 4), configuration.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
      (∀ (index : Fin count) (patch : Fin 4), configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
      (∀ parameter source, (initial parameter).2.2 source = standardCircleBanach) →
      (∀ parameter, ReferenceInitialDisks scales (trajectories parameter).movingFamily.patchMotion phase parameter.val (1 / 2)) →
      0 < margin → 0 ≤ horizon → horizon < forwardHorizon →
      0 < scales.amplitude → 1 ≤ scales.frequency → 2 ≤ scales.ratio → 0 < scales.alpha →
      Continuous (fun point : closedBall (0 : Fin count → ℝ) radius × ℝ => (trajectories point.1).curve point.2) →
      (∀ parameter index, (movingReferenceShapeCoordinates scales ((trajectories parameter).curve 0) index).1 = parameter.val index) →
      ∀ (memory bound : ℝ), 0 ≤ memory → 0 ≤ bound → scales.hessian ≤ 1 →
      (∀ index : Fin count, scales.length (index.val + 1) ≤ 1) →
      (∀ index : Fin count, scales.length (index.val + 1) < momentRadius / (8 * (memory + 1))) →
      (∀ index : Fin count, referenceShapeForcingBudget scales (index.val + 1) internal memory bound ≤
        scales.omega (index.val + 1) * radius / 16) →
      ∀ (deformation : closedBall (0 : Fin count → ℝ) radius → ℝ → Fin count → ℝ),
      (∀ parameter terminal, terminal ∈ Icc 0 horizon →
        (∀ current ∈ Icc 0 terminal, ∀ index,
          |(movingReferenceShapeCoordinates scales ((trajectories parameter).curve current) index).1| ≤ radius) →
        (∀ current ∈ Icc 0 terminal, margin ≤ infDist ((trajectories parameter).curve current)
          (configuration.movingStateAdmissible centerBound shapeRadius gap)ᶜ) ∧
        ∀ time ∈ Icc 0 terminal, ∀ index : Fin count,
          ReferenceCentroidFieldGeometry scales (trajectories parameter).movingFamily.patchMotion time index ∧
          (∀ patch, BoundaryCloseToCircle scales (trajectories parameter).movingFamily.patchMotion time index patch
            (deformation parameter time index)) ∧
          0 ≤ deformation parameter time index ∧ deformation parameter time index ≤ 1 / 16 ∧
          deformation parameter time index ≤ bound / scales.omega (index.val + 1) ^ 2 ∧
          scales.length (index.val + 1) ^ 2 / 2 ≤ diagonalDifference (trajectories parameter).movingFamily.patchMotion time index ∧
          diagonalDifference (trajectories parameter).movingFamily.patchMotion time index ≤ 2 * scales.length (index.val + 1) ^ 2 ∧
          ‖centroidAsymmetry (trajectories parameter).movingFamily.patchMotion time index‖ ≤ memory * scales.length (index.val + 1) ^ 2) →
      ∃ parameter, FinitePatchEvolution scales (trajectories parameter).movingFamily.patchMotion horizon ∧
        ∀ time ∈ Icc 0 horizon, ∀ index : Fin count,
          |unstableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius ∧
          |stableShape (trajectories parameter).movingFamily.patchMotion time index| ≤ radius := by
  obtain ⟨shootInternal, shootInternalNonnegative, shootMoment, shootMomentPositive, shootRadius, shootRadiusPositive, shootRadiusSmall, shooting⟩ :=
    exists_uniform_actual_reference_stopped_shooting
  obtain ⟨barrierInternal, barrierInternalNonnegative, barrierMoment, barrierMomentPositive, barrierRadius, barrierRadiusPositive,
    barrierRadiusSmall, barrier⟩ := FiniteMovingPatchFamily.exists_uniform_unclamped_reference_shape_barrier
  let internal := max shootInternal barrierInternal
  let momentRadius := min shootMoment barrierMoment
  let maximumRadius := min shootRadius barrierRadius
  refine ⟨internal, shootInternalNonnegative.trans (le_max_left _ _), momentRadius, lt_min shootMomentPositive barrierMomentPositive,
    maximumRadius, lt_min shootRadiusPositive barrierRadiusPositive, (min_le_left _ _).trans shootRadiusSmall, ?_⟩
  intro radius radiusPositive radiusBound count configuration centerBound shapeRadius gap margin backwardHorizon forwardHorizon horizon
    scales phase initial trajectories densityIdentity radiusIdentity initialCircles initialDisks marginPositive horizonNonnegative beforeFinal
    amplitudePositive frequencyBound ratioBound alphaPositive jointContinuous initialCoordinate memory bound memoryNonnegative boundNonnegative
    hessianBound lengthBound lengthSmall forcingSmall deformation physical
  have strainNonnegative : 0 ≤ scales.strain := tsum_nonneg fun source =>
    div_nonneg (scales.circulation_pos (zero_lt_one.trans_le frequencyBound) (by linarith) _).le (sq_nonneg _)
  have shootLength (index : Fin count) : scales.length (index.val + 1) < shootMoment / (8 * (memory + 1)) :=
    (lengthSmall index).trans_le (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity))
  have barrierLength (index : Fin count) : scales.length (index.val + 1) < barrierMoment / (8 * (memory + 1)) :=
    (lengthSmall index).trans_le (div_le_div_of_nonneg_right (min_le_right _ _) (by positivity))
  have shootForcing (index : Fin count) : referenceShapeForcingBudget scales (index.val + 1) shootInternal memory bound ≤
      scales.omega (index.val + 1) * radius / 16 :=
    (referenceShapeForcingBudget_mono_internal scales _ (le_max_left _ _) strainNonnegative).trans (forcingSmall index)
  have barrierForcing (index : Fin count) : referenceShapeForcingBudget scales (index.val + 1) barrierInternal memory bound ≤
      scales.omega (index.val + 1) * radius / 16 :=
    (referenceShapeForcingBudget_mono_internal scales _ (le_max_right _ _) strainNonnegative).trans (forcingSmall index)
  have coordinateIdentity (parameter : closedBall (0 : Fin count → ℝ) radius) (time : ℝ)
      (inside : time ∈ Ioo (-backwardHorizon) forwardHorizon) (index : Fin count) :
      movingReferenceShapeCoordinates scales ((trajectories parameter).curve time) index =
        regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
          (positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)
          (negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index) := by
    dsimp only [movingReferenceShapeCoordinates]
    rw [← (trajectories parameter).patchCentroid_eq_curve_center (initialCircles parameter) inside index 0,
      ← (trajectories parameter).patchCentroid_eq_curve_center (initialCircles parameter) inside index 1,
      ← (trajectories parameter).patchCentroid_eq_curve_center (initialCircles parameter) inside index 2,
      ← (trajectories parameter).patchCentroid_eq_curve_center (initialCircles parameter) inside index 3]
    rfl
  apply shooting radius radiusPositive (radiusBound.trans (min_le_left _ _)) scales initial trajectories densityIdentity radiusIdentity
    initialCircles marginPositive horizonNonnegative beforeFinal amplitudePositive frequencyBound ratioBound alphaPositive jointContinuous
    initialCoordinate memory bound memoryNonnegative boundNonnegative hessianBound lengthBound shootLength shootForcing deformation
  intro parameter terminal terminalInside prefixBound
  obtain ⟨safe, conditions⟩ := physical parameter terminal terminalInside prefixBound
  have beforeTerminal : terminal < forwardHorizon := terminalInside.2.trans_lt beforeFinal
  have evolution := (trajectories parameter).finitePatchEvolution_of_margin scales densityIdentity radiusIdentity
    (initialCircles parameter) marginPositive terminalInside.1 beforeTerminal safe
  have inside (time : ℝ) (member : time ∈ Icc 0 terminal) : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨(neg_neg_of_pos (trajectories parameter).backward_positive).trans_le member.1, member.2.trans_lt beforeTerminal⟩
  have material (time : ℝ) (member : time ∈ Icc 0 terminal) (source : Fin (count * 4)) (label : ℝ) :
      ((trajectories parameter).movingFamily.patch source).boundaryVelocity time label =
        biotSavart (Paper.patchVorticity scales (trajectories parameter).movingFamily.patchMotion time)
          (((trajectories parameter).movingFamily.patch source).boundary time label) := by
    have familyDensity : ∀ (index : Fin count) (patch : Fin 4),
        (trajectories parameter).movingFamily.density (finProdFinEquiv (index, patch)) =
          patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4 := densityIdentity
    rw [(trajectories parameter).movingFamily.patchVorticity_eq scales familyDensity]
    exact (trajectories parameter).movingFamily_material_equation_of_margin marginPositive (inside time member) (safe time member) source label
  have initialBound (index : Fin count) : |parameter.val index| ≤ radius := by
    have total : ‖parameter.val‖ ≤ radius := by simpa only [mem_closedBall, dist_zero_right] using parameter.property
    exact (show |parameter.val index| ≤ ‖parameter.val‖ by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm parameter.val index).trans total
  have actualRegularized (time : ℝ) (member : time ∈ Icc 0 terminal) (index : Fin count) :
      |(regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
        (positiveHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)
        (negativeHalfDiagonal (trajectories parameter).movingFamily.patchMotion time index)).1| ≤ radius := by
    simpa only [coordinateIdentity parameter time (inside time member) index] using prefixBound time member index
  have actual := barrier radius radiusPositive (radiusBound.trans (min_le_right _ _)) (trajectories parameter).movingFamily evolution
    terminalInside.1 amplitudePositive frequencyBound ratioBound alphaPositive memoryNonnegative boundNonnegative hessianBound
    (initialDisks parameter) (by norm_num) initialBound
    (fun time member index => (conditions time member index).1) (fun time member source => inside time member) material
    (deformation parameter) (fun time member index => (conditions time member index).2.1)
    (fun time member index => (conditions time member index).2.2.1)
    (fun time member index => (conditions time member index).2.2.2.1)
    (fun time member index => (conditions time member index).2.2.2.2.1) lengthBound
    (fun time member index => (conditions time member index).2.2.2.2.2.1)
    (fun time member index => (conditions time member index).2.2.2.2.2.2.1)
    (fun time member index => (conditions time member index).2.2.2.2.2.2.2) barrierLength actualRegularized barrierForcing
  refine ⟨safe, ?_⟩
  intro index
  obtain ⟨geometry, control, nonnegative, small, deformationBound, differenceLower, differenceUpper, momentBound⟩ :=
    conditions terminal ⟨terminalInside.1, le_rfl⟩ index
  obtain ⟨upper, agreement, unstableBound, stableBound⟩ := actual terminal ⟨terminalInside.1, le_rfl⟩ index
  refine ⟨geometry, control, nonnegative, small, deformationBound, differenceLower, differenceUpper, momentBound, upper, ?_, stableBound.le⟩
  linarith [radiusBound.trans ((min_le_left _ _).trans shootRadiusSmall)]

end EulerNonuniqueness.Paper
