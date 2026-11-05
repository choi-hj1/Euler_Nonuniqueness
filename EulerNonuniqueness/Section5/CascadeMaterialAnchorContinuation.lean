import EulerNonuniqueness.Section5.CascadeMaterialInitialExtent
import EulerNonuniqueness.Section5.CascadeCenterVelocityBound
import EulerNonuniqueness.Section5.CascadeAnchorFrequencyBudget

noncomputable section

open Set Metric Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_cascade_anchor_improvement (scales : Scales)
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
    ∀ time ∈ Icc 0 horizon, ∀ index, cascadeAnchorNormMonitor index
      (prepared.trajectory.movingFamily.cascadeCenters time) < 0 := by
  let bound := max (3 : ℝ) (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  have boundThree : 3 ≤ bound := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (16 * boundaryConstant + 1),
    scales.eventually_cascade_anchor_speed_budget amplitudePositive ratioBound alphaPositive factorPositive factorSmall,
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
  have globalInside (time : ℝ) (inside : time ∈ Icc 0 horizon) : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have fieldIdentity := prepared.trajectory.movingFamily.patchVorticity_eq changed prepared.densityIdentity
  have material (time : ℝ) (inside : time ∈ Icc 0 horizon) (label : Fin (count * 4)) (angle : ℝ) :
      (prepared.trajectory.movingFamily.patch label).boundaryVelocity time angle =
        biotSavart (Paper.patchVorticity changed prepared.trajectory.movingFamily.patchMotion time)
          ((prepared.trajectory.movingFamily.patch label).boundary time angle) := by
    rw [fieldIdentity]
    exact prepared.trajectory.movingFamily_material_equation_of_margin prepared.marginPositive
      (globalInside time inside) (control.2 time inside).1.le label angle
  have initialCenter (index : Fin count) (patch : Fin 4) :
      ‖prepared.trajectory.center (finProdFinEquiv (index, patch)) 0‖ ≤ 201 / 200 := by
    have estimate := cascadeInitialCenter_offset_bound changed orbit sectionTime
      (fun index => phase (index.val + 1)) prepared.unstable (dipoleAngle count) bound
      (fun index => (prepared.referenceInitial index).1.trans thresholdSmall)
      boundThree positiveBound negativeBound (index, patch)
    have triangle := norm_add_le
      (cascadeInitialCenter changed orbit sectionTime (fun index => phase (index.val + 1))
        prepared.unstable (dipoleAngle count) (index, patch) - (changed.location (index.val + 1) : ℂ))
      (changed.location (index.val + 1) : ℂ)
    simp only [sub_add_cancel, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (changed.location_pos _)] at triangle
    rw [prepared.trajectory.center_initial]
    simp only [Equiv.symm_apply_apply]
    linarith [(geometry (index.val + 1)).1, changed.location_le_one (index.val + 1)]
  have velocityBound (time : ℝ) (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4) :
      ‖(prepared.trajectory.velocity time).2.1 (finProdFinEquiv (index, patch))‖ ≤ 1 / 4 :=
    (prepared.trajectory.centerVelocity_bound_of_monitors changed prepared.radiusIdentity (fun _ => rfl)
      control.1 inside (globalInside time inside) amplitudePositive frequencyBound ratioBound alphaPositive
      (material time inside) factorPositive factorSmall (internal time inside) (extent time inside) (lower time inside)
      radiusInternal radiusLocation (coarse time inside) index patch).trans (budget (index.val + 1))
  have centerNorm (time : ℝ) (inside : time ∈ Icc 0 horizon) (index : Fin count) (patch : Fin 4) :
      ‖prepared.trajectory.center (finProdFinEquiv (index, patch)) time‖ ≤ 2 := by
    have growth := norm_image_sub_le_of_norm_deriv_le_segment'
      (fun current (_ : current ∈ Icc (0 : ℝ) horizon) =>
        (prepared.trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) current).hasDerivWithinAt)
      (fun current member => velocityBound current ⟨member.1, member.2.le⟩ index patch) time inside
    have triangle := norm_add_le
      (prepared.trajectory.center (finProdFinEquiv (index, patch)) time -
        prepared.trajectory.center (finProdFinEquiv (index, patch)) 0)
      (prepared.trajectory.center (finProdFinEquiv (index, patch)) 0)
    rw [sub_add_cancel] at triangle
    linarith [initialCenter index patch, inside.2]
  intro time inside index
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4))
    (fun patch => prepared.trajectory.center (finProdFinEquiv (index, patch)) time)
  have total := Finset.sum_le_sum
    (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => centerNorm time inside index patch)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  norm_num at total
  change ‖(∑ patch : Fin 4, prepared.trajectory.center (finProdFinEquiv (index, patch)) time) / 4‖ - 3 < 0
  rw [norm_div, Complex.norm_ofNat]
  linarith

end EulerNonuniqueness.Paper

