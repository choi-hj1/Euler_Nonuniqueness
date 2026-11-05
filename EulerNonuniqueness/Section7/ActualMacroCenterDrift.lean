import EulerNonuniqueness.Section7.ActualMacroDriftBudget
import EulerNonuniqueness.Section5.CascadeCenterVelocityBound
import EulerNonuniqueness.Section5.CascadeCoMovingPreparedInitial
import EulerNonuniqueness.Section6.SourcePacketActualPostHitContinuation
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_macro_center_drift (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    {factor scaleRoot boundaryConstant budget : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) (budgetPositive : 0 < budget) :
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant shapeRadius monitor : ℝ} {count : ℕ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop, ∀ index : Fin count,
      ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index -
        (({scales with frequency := frequency} : Scales).location (index.val + 1) : ℂ)‖ ≤ budget * time := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_absolute_speed_arbitrary_budget amplitudePositive ratioBound alphaPositive factorPositive factorSmall budgetPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive factorPositive factorSmall
      (by norm_num : (3 : ℝ) ≤ 3),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive factorPositive rootPositive boundaryNonnegative
      (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne speed geometry budgets
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant shapeRadius monitor count prepared path time inside index
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have globalInside (current : ℝ) (member : current ∈ Icc 0 path.stop) : current ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [member.1], by linarith [member.2, path.stopBound]⟩
  have radiusInternal (source : Fin count) := (geometry (source.val + 1)).2.1
  have radiusLocation (source : Fin count) : changed.radius (source.val + 1) ≤ factor * changed.location (source.val + 1) / 1000 := by
    have weighted := mul_le_mul_of_nonneg_left (geometry (source.val + 1)).2.2.1 factorPositive.le
    have locationPositive := changed.location_pos (source.val + 1)
    nlinarith [radiusInternal source]
  have coarse (current : ℝ) (member : current ∈ Icc 0 path.stop) (source : Fin count) (patch : Fin 4) :
      BoundaryCloseToCircle changed prepared.trajectory.movingFamily.patchMotion current source patch (1 / 16) := by
    obtain ⟨relabeling, periodic, relabelingBound, error⟩ := path.boundary current member source patch
    exact ⟨relabeling, periodic, relabelingBound, error.mono (budgets.2 count source).1⟩
  have velocityBound (current : ℝ) (member : current ∈ Icc 0 path.stop) (patch : Fin 4) :
      ‖(prepared.trajectory.velocity current).2.1 (finProdFinEquiv (index, patch))‖ ≤ budget :=
    (prepared.trajectory.centerVelocity_bound_of_monitors changed prepared.radiusIdentity (fun _ => rfl) path.evolution
      member (globalInside current member) amplitudePositive frequencyOne ratioBound alphaPositive
      (fun label angle => path.material_boundary member label angle) factorPositive factorSmall (path.internalClosed current member)
      (fun label => (path.externalMonitors current member (.extent label)).le)
      (fun first second => (path.externalMonitors current member (.lower first second)).le)
      radiusInternal radiusLocation (coarse current member) index patch).trans (speed (index.val + 1))
  let blockPath := fun current => (∑ patch : Fin 4, prepared.trajectory.center (finProdFinEquiv (index, patch)) current) / 4
  let blockVelocity := fun current => (∑ patch : Fin 4, (prepared.trajectory.velocity current).2.1 (finProdFinEquiv (index, patch))) / 4
  have derivative (current : ℝ) : HasDerivAt blockPath (blockVelocity current) current :=
    (HasDerivAt.sum (u := Finset.univ) fun patch _ =>
      prepared.trajectory.center_hasDerivAt (finProdFinEquiv (index, patch)) current).div_const 4
  have blockVelocityBound (current : ℝ) (member : current ∈ Icc 0 path.stop) : ‖blockVelocity current‖ ≤ budget := by
    have triangle := norm_sum_le (Finset.univ : Finset (Fin 4))
      (fun patch => (prepared.trajectory.velocity current).2.1 (finProdFinEquiv (index, patch)))
    have total := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => velocityBound current member patch)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at total
    dsimp only [blockVelocity]
    rw [norm_div, Complex.norm_ofNat]
    linarith
  have initial : blockPath 0 = (changed.location (index.val + 1) : ℂ) := by
    dsimp only [blockPath]
    simp only [prepared.trajectory.center_initial, Equiv.symm_apply_apply]
    exact cascadeBlockCenter_initial changed orbit sectionTime _ prepared.unstable _ index
  have growth := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun current (_ : current ∈ Icc (0 : ℝ) path.stop) => (derivative current).hasDerivWithinAt)
    (fun current member => blockVelocityBound current ⟨member.1, member.2.le⟩) time inside
  have actual : quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index = blockPath time := by
    unfold quadrupoleCenter
    congr 1
    exact Finset.sum_congr rfl (fun patch _ =>
      (prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside time inside) index patch).symm)
  rw [actual]
  simpa only [initial, sub_zero] using growth

end EulerNonuniqueness.Paper
