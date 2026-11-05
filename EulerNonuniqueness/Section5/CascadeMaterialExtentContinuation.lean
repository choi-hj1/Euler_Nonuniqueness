import EulerNonuniqueness.Section5.CascadeMaterialInitialExtent
import EulerNonuniqueness.Section5.CascadeMonitoredExtentImprovement
import EulerNonuniqueness.Section5.CascadeExtentFrequencyBudget

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_cascade_extent_improvement (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (thresholdSmall : threshold ≤ 1 / 2) (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ horizon : ℝ, 0 ≤ horizon → horizon ≤ 1 →
    (∀ time ∈ Icc 0 horizon, ∀ receiver source, cascadeInternalGapMonitor {scales with frequency := frequency}
      factor receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 horizon, ∀ label, cascadeExtentMonitor {scales with frequency := frequency}
      label (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 horizon, ∀ receiver source, cascadeAnchorLowerMonitor {scales with frequency := frequency}
      receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 horizon, ∀ index, cascadeAnchorNormMonitor index
      (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    ∀ time ∈ Icc 0 horizon, ∀ label, cascadeExtentMonitor {scales with frequency := frequency}
      label (prepared.trajectory.movingFamily.cascadeCenters time) < 0 := by
  let bound := max (3 : ℝ) (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  have boundThree : 3 ≤ bound := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (16 * boundaryConstant + 1),
    scales.eventually_cascade_extent_gronwall_budget amplitudePositive ratioBound alphaPositive factorPositive factorSmall,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall boundThree]
    with frequency frequencyLarge budget geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared horizon horizonNonnegative horizonBound
    internal extent lower anchor
  let changed : Scales := {scales with frequency := frequency}
  have frequencyBound : 1 ≤ changed.frequency := by change 1 ≤ frequency; linarith
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have rootPositive : 0 < scaleRoot := by linarith
  have control := prepared.analyticControl horizon horizonNonnegative horizonBound internal extent lower anchor
  have coarse (time : ℝ) (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed prepared.trajectory.movingFamily.patchMotion time index patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, error⟩ := (control.2 time inside).2.2 index patch
    refine ⟨relabeling, periodic, relabelingBound, error.mono ?_⟩
    have omegaBound := changed.omega_ge_frequency frequencyPositive (by linarith) (index.val + 1)
    have omegaPositive := changed.omega_pos frequencyPositive (by linarith) (index.val + 1)
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos rootPositive) (sq_pos_of_pos omegaPositive))).mpr
    have rootSquare : (1 : ℝ) ≤ scaleRoot ^ 2 := by nlinarith
    have denominator := mul_le_mul_of_nonneg_right rootSquare (sq_nonneg (changed.omega (index.val + 1)))
    nlinarith
  have radiusInternal (index : Fin count) := (geometry (index.val + 1)).2.1
  have radiusLocation (index : Fin count) : changed.radius (index.val + 1) ≤
      factor * changed.location (index.val + 1) / 1000 := by
    have weighted := mul_le_mul_of_nonneg_left (geometry (index.val + 1)).2.2.1 factorPositive.le
    have locationPositive := changed.location_pos (index.val + 1)
    nlinarith [radiusInternal index]
  have initialExtent (index : Fin count) : ‖prepared.trajectory.blockExtentVector index 0‖ ≤
      changed.location (index.val + 1) / 200 :=
    (prepared.initial_extent_bound thresholdSmall boundThree positiveBound negativeBound index).trans
      (geometry (index.val + 1)).1
  have strict := prepared.trajectory.blockExtentVector_lt_of_monitored_material_prefix changed
    prepared.densityIdentity prepared.radiusIdentity (fun _ => rfl) amplitudePositive frequencyBound ratioBound alphaPositive
    horizonNonnegative horizonBound (by linarith) prepared.marginPositive
    (fun time inside => (control.2 time inside).1.le) factorPositive factorSmall internal extent lower
    radiusInternal radiusLocation coarse initialExtent (budget 0).1 (fun index => (budget (index.val + 1)).2)
  intro time inside label
  have estimate := (norm_le_pi_norm (prepared.trajectory.blockExtentVector label.1 time) label.2).trans_lt
    (strict time inside label.1)
  change ‖prepared.trajectory.blockExtentVector label.1 time label.2‖ - changed.location (label.1.val + 1) / 100 < 0
  exact sub_neg.mpr estimate

end EulerNonuniqueness.Paper
