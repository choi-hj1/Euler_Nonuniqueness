import EulerNonuniqueness.Section4.ReferenceMonitoredBootstrap

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

theorem exists_uniform_reference_monitored_capped_bootstrap (cap : ℝ) (capPositive : 0 < cap) :
    ∃ monitor > 0, monitor ≤ cap ∧ ∃ boundaryConstant ≥ (1 : ℝ), ∃ memory ≥ (1 : ℝ),
    ∃ diagonalConstant ≥ (0 : ℝ), ∃ internal ≥ (0 : ℝ),
    ∃ momentRadius > (0 : ℝ), ∃ maximumRadius > (0 : ℝ), maximumRadius ≤ 1 / 8 ∧
    ∀ radius : ℝ, 0 < radius → radius ≤ maximumRadius →
    ∀ shapeRadius : ℝ, 0 < shapeRadius → ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ReferenceMechanicalScaleBounds scales diagonalConstant internal memory (boundaryConstant / scaleRoot ^ 2) momentRadius radius →
    ∀ {count : ℕ}, 0 < count → ∀ {configuration : FiniteContourConfiguration (count * 4)}
      {gap margin : ℝ} {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin 1 3 initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ label, initial.2.2 label = standardCircleBanach) → initial.1 = 0 →
    0 < margin → margin ≤ shapeRadius / 8 → margin ≤ 1 / 8 →
    (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * referencePairCutoffSlack scales first second) →
    ∀ {phase unstable : Fin count → ℝ},
    ReferenceInitialDisks scales trajectory.movingFamily.patchMotion phase unstable (1 / 2) →
    (∀ index, |unstable index| ≤ radius) →
    (∀ index, referenceMechanicalMonitor configuration scales shapeRadius gap margin
      (referenceMechanicalShapeStop monitor shapeRadius) initial index < 0) →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ 2 →
    (∀ current ∈ Icc 0 terminal, ∀ label, (trajectory.curve current).2.2 label ∈ contourContinuousVectorSubmodule) →
    (∀ current ∈ Icc 0 terminal, ∀ index,
      |(movingReferenceShapeCoordinates scales (trajectory.curve current) index).1| ≤ radius) →
    ∀ current ∈ Icc 0 terminal, ∀ index,
      referenceMechanicalMonitor configuration scales shapeRadius gap margin
        (referenceMechanicalShapeStop monitor shapeRadius) (trajectory.curve current) index < 0 := by
  obtain ⟨originalMonitor, originalMonitorPositive, boundaryConstant, boundaryOne, contourImprovements⟩ :=
    exists_uniform_reference_mechanical_contour_improvement_on_horizon
  obtain ⟨memory, memoryOne, diagonalConstant, diagonalNonnegative, internal, internalNonnegative,
    momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, prefixImprovements⟩ :=
    exists_uniform_reference_geometric_monitor_improvement
  let monitor := min originalMonitor cap
  have monitorPositive : 0 < monitor := lt_min originalMonitorPositive capPositive
  refine ⟨monitor, monitorPositive, min_le_right _ _, boundaryConstant, boundaryOne, memory, memoryOne, diagonalConstant, diagonalNonnegative,
    internal, internalNonnegative, momentRadius, momentPositive, maximumRadius, maximumPositive, maximumSmall, ?_⟩
  intro radius radiusPositive radiusBound shapeRadius shapePositive
  let shapeStop := referenceMechanicalShapeStop monitor shapeRadius
  have stopBounds := referenceMechanicalShapeStop_bounds monitorPositive shapePositive
  obtain ⟨rootMin, rootEight, contourImproved⟩ := contourImprovements 2 shapeStop (by norm_num) stopBounds.1
  refine ⟨rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive scaleBounds count countPositive configuration gap margin initial
    trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive marginShape marginUnit marginSlack
    phase unstable initialDisks initialBound initialStrict terminal terminalNonnegative terminalBound shapeMember unstableBound
  have rootPositive : 0 < scaleRoot := by linarith [rootEight.trans rootLarge]
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have boundNonnegative : 0 ≤ boundaryConstant / scaleRoot ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have radiusSmall (index : Fin count) : scales.radius (index.val + 1) ≤ scales.length (index.val + 1) / 1000 := by
    have positive := scales.radius_pos amplitudePositive (zero_lt_one.trans_le scaleBounds.frequencyLarge)
      (by linarith) (index.val + 1)
    linarith [scaleBounds.radiusSmall (index.val + 1)]
  apply referenceMechanicalMonitor_confined_of_strict_prefix_improvement configuration scales shapeRadius gap margin shapeStop
    trajectory.continuous.continuousOn
  · simpa only [trajectory.initial_identity] using initialStrict
  intro time timeMember closed strict
  by_cases atInitial : time = 0
  · subst time
    simpa only [trajectory.initial_identity] using initialStrict
  have timePositive : 0 < time := lt_of_le_of_ne timeMember.1 (Ne.symm atInitial)
  have timeBound : time ≤ 2 := timeMember.2.trans terminalBound
  have beforeFinal : time < 3 := by linarith
  have inside (current : ℝ) (member : current ∈ Icc 0 time) : current ∈ Ioo (-1 : ℝ) 3 := by
    constructor <;> linarith [member.1, member.2]
  have decoded (current : ℝ) (member : current ∈ Icc 0 time) :=
    trajectory.reference_paper_geometry_of_nonpositive_monitors scales initialCircles (inside current member) (closed current member)
  have contour := contourImproved scales scaleRoot rootLarge time timePositive.le timeBound amplitudeIdentity
    scaleBounds.frequencyLarge ratioLarge alphaPositive scaleBounds.strainSmall trajectory densityIdentity radiusIdentity
    initialCircles initialClock marginPositive beforeFinal
    (fun current member => (decoded current member).1)
    (fun current member => referenceMechanicalMonitor_strict_clearance (strict current member .clearance))
    (fun index => scaleBounds.lengthSmall (index.val + 1)) radiusSmall
    (fun current member index => ((decoded current member).2.1 index).1)
    (fun current member index => ((decoded current member).2.1 index).2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.2.1)
    (fun current member index => ((decoded current member).2.1 index).2.2.1)
    (fun current member receiver source different => ((decoded current member).2.2 receiver source different).1)
    (fun current member label => ((referenceMechanicalMonitor_shape label (closed current member (.shape label))).trans_lt
      stopBounds.2.1).trans_le (min_le_left _ _))
    (fun current member label => shapeMember current ⟨member.1, member.2.trans timeMember.2⟩ label)
  apply prefixImprovements radius radiusPositive radiusBound countPositive trajectory scales densityIdentity radiusIdentity
    initialCircles initialClock shapePositive marginPositive marginShape marginUnit marginSlack timePositive timeBound beforeFinal
    amplitudePositive scaleBounds.frequencyLarge ratioLarge alphaPositive stopBounds.2.2.2 stopBounds.2.2.1 boundNonnegative
    (by norm_num : (0 : ℝ) ≤ 1 / 57600)
    (fun index => scaleBounds.lengthSmall (index.val + 1)) (fun index => scaleBounds.radiusSmall (index.val + 1))
    (fun index => scaleBounds.omegaLength (index.val + 1)) (fun index => scaleBounds.relativeOmegaLength (index.val + 1))
    initialDisks (by norm_num) initialBound closed
    (fun current member index => unstableBound current ⟨member.1, member.2.trans timeMember.2⟩ index)
    (fun label => contour.1 time ⟨timePositive.le, le_rfl⟩ label)
    (by
      intro current member index patch
      simpa only [div_div] using contour.2 current member index patch)
    (fun index => scaleBounds.deformationSmall (index.val + 1)) scaleBounds.strainSmall scaleBounds.hessianSmall
    (fun index => scaleBounds.neutralSmall (index.val + 1)) (fun index => scaleBounds.momentSmall (index.val + 1))
    (fun index => scaleBounds.forcingSmall (index.val + 1)) scaleBounds.diagonalBudget scaleBounds.pairBudget scaleBounds.absoluteBudget

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

