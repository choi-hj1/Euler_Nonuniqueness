import EulerNonuniqueness.Section5.CascadeMaterialInitialExtent
import EulerNonuniqueness.Section5.CascadeAnchorPairVelocity
import EulerNonuniqueness.Section5.CascadePairStrainBudget
import EulerNonuniqueness.Section5.CascadeExtentFrequencyBudget

noncomputable section

open Set Metric Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.eventually_material_cascade_anchor_vector_drift (scales : Scales)
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
    (∀ time ∈ Icc 0 horizon, ∀ receiver source, cascadeAnchorUpperMonitor {scales with frequency := frequency}
      receiver source (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    (∀ time ∈ Icc 0 horizon, ∀ index, cascadeAnchorNormMonitor index
      (prepared.trajectory.movingFamily.cascadeCenters time) ≤ 0) →
    ∀ time ∈ Icc 0 horizon, ∀ first second : Fin count,
      ‖(quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time first -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time second) -
        (({scales with frequency := frequency} : Scales).location (first.val + 1) -
          (({scales with frequency := frequency} : Scales).location (second.val + 1) : ℂ))‖ ≤
        |({scales with frequency := frequency} : Scales).location (first.val + 1) -
          ({scales with frequency := frequency} : Scales).location (second.val + 1)| / 8 := by
  let bound := max (3 : ℝ) (max ‖orbit.positive sectionTime‖ ‖orbit.negative sectionTime‖)
  have boundThree : 3 ≤ bound := le_max_left _ _
  have positiveBound : ‖orbit.positive sectionTime‖ ≤ bound := (le_max_left _ _).trans (le_max_right _ _)
  have negativeBound : ‖orbit.negative sectionTime‖ ≤ bound := (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [eventually_ge_atTop (16 * boundaryConstant + 1),
    scales.eventually_cascade_extent_gronwall_budget amplitudePositive ratioBound alphaPositive factorPositive factorSmall,
    scales.eventually_cascade_pair_strain_budget ratioBound alphaPositive factorPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall boundThree]
    with frequency frequencyLarge budget strainBudgets geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared horizon horizonNonnegative horizonBound
    internal extent lower upper anchor
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
  intro time inside first second
  by_cases same : first = second
  · simp [same]
  let pairPath := fun current =>
    (∑ patch : Fin 4, prepared.trajectory.center (finProdFinEquiv (first, patch)) current) / 4 -
    (∑ patch : Fin 4, prepared.trajectory.center (finProdFinEquiv (second, patch)) current) / 4
  let pairVelocity := fun current =>
    (∑ patch : Fin 4, (prepared.trajectory.velocity current).2.1 (finProdFinEquiv (first, patch))) / 4 -
    (∑ patch : Fin 4, (prepared.trajectory.velocity current).2.1 (finProdFinEquiv (second, patch))) / 4
  have derivative (current : ℝ) : HasDerivAt pairPath (pairVelocity current) current :=
    ((HasDerivAt.sum (u := Finset.univ) fun patch _ =>
      prepared.trajectory.center_hasDerivAt (finProdFinEquiv (first, patch)) current).div_const 4).sub
    ((HasDerivAt.sum (u := Finset.univ) fun patch _ =>
      prepared.trajectory.center_hasDerivAt (finProdFinEquiv (second, patch)) current).div_const 4)
  have velocityBound (current : ℝ) (member : current ∈ Icc 0 horizon) :
      ‖pairVelocity current‖ ≤ |changed.location (first.val + 1) - changed.location (second.val + 1)| / 8 :=
    prepared.trajectory.blockAnchorPairVelocity_bound_of_monitors changed prepared.radiusIdentity (fun _ => rfl)
      control.1 member (globalInside current member) amplitudePositive frequencyBound ratioBound alphaPositive
      (material current member) factorPositive factorSmall (internal current member) (extent current member)
      (lower current member) (upper current member) radiusInternal radiusLocation (coarse current member)
      (fun index => (budget (index.val + 1)).2) strainBudgets.1 strainBudgets.2 first second same
  have initialPair : pairPath 0 =
      (changed.location (first.val + 1) : ℂ) - (changed.location (second.val + 1) : ℂ) := by
    dsimp only [pairPath]
    simp only [prepared.trajectory.center_initial, Equiv.symm_apply_apply]
    exact congrArg₂ (fun first second : ℂ => first - second)
      (cascadeBlockCenter_initial changed orbit sectionTime _ prepared.unstable _ first)
      (cascadeBlockCenter_initial changed orbit sectionTime _ prepared.unstable _ second)
  have growth := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current (_ : current ∈ Icc (0 : ℝ) horizon) => (derivative current).hasDerivWithinAt)
    (fun current member => velocityBound current ⟨member.1, member.2.le⟩) time inside
  rw [initialPair, sub_zero] at growth
  have gapPositive := changed.location_distance_pos
    (show first.val + 1 ≠ second.val + 1 from fun equal => same (Fin.ext (Nat.add_right_cancel equal)))
  have growthSmall : ‖pairPath time - ((changed.location (first.val + 1) : ℂ) -
      (changed.location (second.val + 1) : ℂ))‖ ≤
      |changed.location (first.val + 1) - changed.location (second.val + 1)| / 8 :=
    growth.trans (mul_le_of_le_one_right (by positivity) (inside.2.trans horizonBound))
  have actualCenters (index : Fin count) :
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index =
        (∑ patch : Fin 4, prepared.trajectory.center (finProdFinEquiv (index, patch)) time) / 4 := by
    unfold quadrupoleCenter
    congr 1
    apply Finset.sum_congr rfl
    intro patch member
    exact (prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) index patch).symm
  rw [actualCenters first, actualCenters second]
  exact growthSmall

end EulerNonuniqueness.Paper

