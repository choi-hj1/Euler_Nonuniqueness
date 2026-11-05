import EulerNonuniqueness.Section5.CascadeContourShapeHorizonImprovement
import EulerNonuniqueness.Section5.CascadeContourBoundaryHorizonImprovement
import EulerNonuniqueness.Section5.CascadeCutoffSafety
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section

open Set Metric

namespace EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] normalizedUniformSlopeC1Group chartedBilinearC1Space
  canonicalForcingAddCommGroup canonicalForcingAdd canonicalForcingZero canonicalForcingNeg canonicalForcingSub

theorem exists_uniform_cascade_analytic_bootstrap
    (factor : ℝ) (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∃ monitor > 0, ∃ boundaryConstant ≥ (1 : ℝ),
    ∀ shapeRadius horizon : ℝ, 0 < shapeRadius → 0 ≤ horizon →
    ∃ rootMin ≥ (8 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot →
    scales.amplitude = scaleRoot ^ 3 → 1 ≤ scales.frequency → 2 ≤ scales.ratio →
    0 < scales.alpha → scales.strain ≤ 1 →
    ∀ {count : ℕ}, 0 < count → ∀ {configuration : FiniteContourConfiguration (count * 4)}
      {gap margin backwardHorizon forwardHorizon : ℝ} {initial : MovingContourState (count * 4)}
      (trajectory : MovingCentroidGaugeTrajectory configuration 4 shapeRadius gap margin
        backwardHorizon forwardHorizon initial),
    (∀ index patch, configuration.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4) →
    (∀ index patch, configuration.radius (finProdFinEquiv (index, patch)) = scales.radius (index.val + 1)) →
    (∀ label, initial.2.2 label = standardCircleBanach) → initial.1 = 0 →
    0 < margin → margin ≤ shapeRadius / 8 → margin ≤ 1 / 8 →
    (∀ first second : Fin count × Fin 4, gap + 4 * margin ≤ 4 * cascadePairCutoffSlack scales factor first second) →
    2 * margin ≤ infDist (trajectory.curve 0) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ →
    (∀ index : Fin count, scales.length (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ factor * scales.length (index.val + 1) / 1000) →
    (∀ index : Fin count, scales.radius (index.val + 1) ≤ scales.location (index.val + 1) / 1000) →
    ∀ terminal : ℝ, 0 ≤ terminal → terminal ≤ horizon → terminal < forwardHorizon →
    (∀ time ∈ Icc 0 terminal, ∀ receiver source,
      cascadeInternalGapMonitor scales factor receiver source (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 terminal, ∀ label,
      cascadeLocationMonitor scales label (trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 terminal, ∀ label, (trajectory.curve time).2.2 label ∈ contourContinuousVectorSubmodule) →
    FinitePatchEvolution scales trajectory.movingFamily.patchMotion terminal ∧
    ∀ time ∈ Icc 0 terminal,
      margin < infDist (trajectory.curve time) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ ∧
      (∀ label, ‖(trajectory.curve time).2.2 label - standardCircleBanach‖ < min (monitor / 2) (shapeRadius / 2)) ∧
      ∀ index patch, BoundaryCloseToCircle scales trajectory.movingFamily.patchMotion time index patch
        (boundaryConstant / (scaleRoot ^ 2 * scales.omega (index.val + 1) ^ 2)) := by
  obtain ⟨shapeMonitor, shapeMonitorPositive, shapes⟩ :=
    exists_uniform_cascade_shape_improvement_on_horizon factor factorPositive factorSmall
  obtain ⟨boundaryMonitor, boundaryMonitorPositive, boundaryConstant, boundaryOne, boundaries⟩ :=
    exists_uniform_cascade_boundary_improvement_on_horizon factor factorPositive factorSmall
  let monitor := min shapeMonitor boundaryMonitor
  have monitorPositive : 0 < monitor := lt_min shapeMonitorPositive boundaryMonitorPositive
  refine ⟨monitor, monitorPositive, boundaryConstant, boundaryOne, ?_⟩
  intro shapeRadius horizon shapePositive horizonNonnegative
  let stop := min (monitor / 2) (shapeRadius / 2)
  have stopPositive : 0 < stop := lt_min (half_pos monitorPositive) (half_pos shapePositive)
  have stopShape : stop < shapeMonitor :=
    (min_le_left _ _).trans_lt ((by linarith : monitor / 2 < monitor).trans_le (min_le_left _ _))
  have stopBoundary : stop < boundaryMonitor :=
    (min_le_left _ _).trans_lt ((by linarith : monitor / 2 < monitor).trans_le (min_le_right _ _))
  obtain ⟨shapeRoot, shapeRootEight, shapeImproved⟩ := shapes horizon (stop / 2) horizonNonnegative (half_pos stopPositive)
  obtain ⟨boundaryRoot, boundaryRootEight, boundaryImproved⟩ := boundaries horizon horizonNonnegative
  refine ⟨max shapeRoot boundaryRoot, shapeRootEight.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
    count countPositive configuration gap margin backwardHorizon forwardHorizon initial trajectory
    densityIdentity radiusIdentity initialCircles initialClock marginPositive marginShape marginUnit marginSlack
    initialMargin lengthSmall radiusInternal radiusLocation terminal terminalNonnegative terminalBound beforeFinal
    internal offset shapeMember
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 terminal) : time ∈ Ioo (-backwardHorizon) forwardHorizon :=
    ⟨by linarith [trajectory.backward_positive, inside.1], inside.2.trans_lt beforeFinal⟩
  have centersEqual (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      trajectory.movingFamily.cascadeCenters time = fun label => (trajectory.curve time).2.1 (finProdFinEquiv label) := by
    funext label
    exact trajectory.center_eq_curve (globalInside time inside) (finProdFinEquiv label)
  let observable : Option (Fin (count * 4)) → ℝ → ℝ := fun index time => match index with
    | none => margin - infDist (trajectory.curve time) (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ
    | some label => ‖(trajectory.curve time).2.2 label - standardCircleBanach‖ - stop
  have continuous (index : Option (Fin (count * 4))) : ContinuousOn (observable index) (Icc 0 terminal) := by
    cases index with
    | none => exact (continuous_const.sub ((continuous_infDist_pt _).comp trajectory.continuous)).continuousOn
    | some label => exact ((((continuous_apply label).comp trajectory.continuous.snd.snd).sub continuous_const).norm.sub continuous_const).continuousOn
  have initialStrict (index : Option (Fin (count * 4))) : observable index 0 < 0 := by
    cases index with
    | none => change margin - _ < 0; linarith
    | some label =>
      change ‖(trajectory.curve 0).2.2 label - standardCircleBanach‖ - stop < 0
      rw [trajectory.initial_identity, initialCircles label, sub_self, norm_zero, zero_sub]
      exact neg_neg_of_pos stopPositive
  have confined := EulerNonuniqueness.General.finite_strictly_negative_of_strict_prefix_improvement continuous initialStrict
    (by
      intro time inside closed strict
      have safe (current : ℝ) (member : current ∈ Icc 0 time) : margin ≤ infDist (trajectory.curve current)
          (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := sub_nonpos.mp (closed current member none)
      have strictSafe (current : ℝ) (member : current ∈ Ico 0 time) : margin < infDist (trajectory.curve current)
          (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := sub_neg.mp (strict current member none)
      have small (current : ℝ) (member : current ∈ Icc 0 time) (label : Fin (count * 4)) :
          ‖(trajectory.curve current).2.2 label - standardCircleBanach‖ ≤ stop := sub_nonpos.mp (closed current member (some label))
      have prefixMember {current : ℝ} (member : current ∈ Icc 0 time) : current ∈ Icc 0 terminal :=
        ⟨member.1, member.2.trans inside.2⟩
      have improved := shapeImproved scales scaleRoot ((le_max_left _ _).trans rootLarge) time inside.1
        (inside.2.trans terminalBound) amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall
        trajectory densityIdentity radiusIdentity initialCircles initialClock marginPositive (inside.2.trans_lt beforeFinal)
        safe strictSafe (fun current member => internal current (prefixMember member))
        (fun current member => offset current (prefixMember member)) lengthSmall radiusInternal radiusLocation
        (fun current member label => (small current member label).trans_lt stopShape)
        (fun current member label => shapeMember current (prefixMember member) label)
      have clearance := cascade_cutoff_margin_of_nonpositive_geometric_monitors countPositive scales configuration
        (trajectory.curve time) factorPositive radiusIdentity marginShape marginUnit marginSlack
        (by rw [← centersEqual time inside]; exact internal time inside)
        (by rw [← centersEqual time inside]; exact offset time inside) radiusInternal radiusLocation
        (fun label => (small time ⟨inside.1, le_rfl⟩ label).trans (min_le_right _ _))
      intro index
      cases index with
      | none => change margin - _ < 0; linarith
      | some label =>
        change ‖(trajectory.curve time).2.2 label - standardCircleBanach‖ - stop < 0
        have estimate := improved time ⟨inside.1, le_rfl⟩ label
        linarith)
  have safe (time : ℝ) (inside : time ∈ Icc 0 terminal) : margin ≤ infDist (trajectory.curve time)
      (configuration.movingStateAdmissible 4 shapeRadius gap)ᶜ := (sub_neg.mp (confined time inside none)).le
  have boundary := boundaryImproved scales scaleRoot ((le_max_right _ _).trans rootLarge) terminal terminalNonnegative
    terminalBound amplitudeIdentity frequencyLarge ratioLarge alphaPositive strainSmall trajectory densityIdentity radiusIdentity
    initialCircles initialClock marginPositive beforeFinal safe
    (fun time inside => sub_neg.mp (confined time ⟨inside.1, inside.2.le⟩ none))
    internal offset lengthSmall radiusInternal radiusLocation
    (fun time inside label => (sub_neg.mp (confined time inside (some label))).trans stopBoundary) shapeMember
  refine ⟨trajectory.finitePatchEvolution_of_margin scales densityIdentity radiusIdentity initialCircles marginPositive
    terminalNonnegative beforeFinal safe, ?_⟩
  intro time inside
  exact ⟨sub_neg.mp (confined time inside none),
    fun label => sub_neg.mp (confined time inside (some label)), boundary time inside⟩

end EulerNonuniqueness.Paper.MovingCentroidGaugeTrajectory
