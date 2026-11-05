import EulerNonuniqueness.Section5.CascadePostHitScalarBudget
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section5.CascadeMaterialForeignGeometry
import EulerNonuniqueness.Section7.PaperDipoleDynamics
import EulerNonuniqueness.Section6.MovingBlockCenteredForcingBound
import EulerNonuniqueness.Section6.ContinuedForcedDipoleSeparation
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set Metric Filter
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_material_centered_forcing_bound (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ time ∈ Icc 0 path.stop,
      ‖quadrupoleCenteredForcing {scales with frequency := frequency}
          prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        (1 / 2048 : ℝ) *
          (‖fourPointCenterProjection (fun patch => patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch)‖ +
            ({scales with frequency := frequency} : Scales).length (index.val + 1)) := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive
      factorPositive rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1 / 4096),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyLarge budgets geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index time inside
  let start : ℝ := 0
  let horizon : ℝ := path.stop
  have startNonnegative : 0 ≤ start := le_rfl
  have horizonNonnegative : 0 ≤ horizon := path.stopPositive.le
  have endBound : start + horizon ≤ path.stop := by simp only [start, horizon, zero_add, le_refl]
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let length := changed.length (index.val + 1)
  let deformation := boundaryConstant / (scaleRoot ^ 2 * omega ^ 2)
  have frequencyOne : 1 ≤ changed.frequency := by change 1 ≤ frequency; linarith
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaLarge : 64 ≤ omega := frequencyLarge.trans
    (changed.omega_ge_frequency frequencyPositive (by linarith) _)
  have lengthPositive : 0 < length := changed.length_pos _
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have globalInside (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [(timeRange elapsed inside).1], by linarith [(timeRange elapsed inside).2, path.stopBound]⟩
  have extent (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin count × Fin 4) :=
    (path.externalMonitors (start + elapsed) (timeRange elapsed inside) (.extent label)).le
  have lower (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (receiver source : Fin count) :=
    (path.externalMonitors (start + elapsed) (timeRange elapsed inside) (.lower receiver source)).le
  have radiusInternal (source : Fin count) : changed.radius (source.val + 1) ≤
      factor * changed.length (source.val + 1) / 1000 := (geometry (source.val + 1)).2.1
  have radiusLocation (source : Fin count) : changed.radius (source.val + 1) ≤
      factor * changed.location (source.val + 1) / 1000 := by
    have bound := mul_le_mul_of_nonneg_left (geometry (source.val + 1)).2.2.1 factorPositive.le
    change factor * changed.length (source.val + 1) ≤ factor * (changed.location (source.val + 1) / 1000) at bound
    calc
      _ ≤ factor * changed.length (source.val + 1) / 1000 := radiusInternal source
      _ ≤ factor * changed.length (source.val + 1) := by
        have positive := mul_pos factorPositive (changed.length_pos (source.val + 1))
        linarith
      _ ≤ _ := by linarith
  have foreign (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (source : Fin count)
      (member : source ∈ Finset.univ.erase index) :=
    prepared.trajectory.cascade_foreign_geometry_of_monitors changed prepared.radiusIdentity (fun _ => rfl)
      (globalInside elapsed inside) factorPositive factorSmall (extent elapsed inside) (lower elapsed inside)
      radiusLocation index source (Finset.mem_erase.mp member).1
  let region := fun elapsed => Set.range (fun patch => patchCentroid motion (start + elapsed) index patch)
  have separated (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ∀ position ∈ region elapsed, ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ motion.domain (start + elapsed) source patch,
        cascadeForeignDistance changed factor index source ≤ ‖position - location‖ := by
    rintro position ⟨target, rfl⟩ source member patch location locationInside
    exact (foreign elapsed inside source member).2.2.2.2.1 target patch location locationInside
  have sourceBounded (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (source : Fin count) (patch : Fin 4) :=
    prepared.trajectory.domain_subset_centroid_ball changed prepared.radiusIdentity (fun _ => rfl)
      (globalInside elapsed inside) source patch
  have fieldIdentity := prepared.trajectory.movingFamily.patchVorticity_eq changed prepared.densityIdentity
  have material (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (label : Fin (count * 4)) (angle : ℝ) :
      (prepared.trajectory.movingFamily.patch label).boundaryVelocity (start + elapsed) angle =
        biotSavart (Paper.patchVorticity changed motion (start + elapsed))
          ((prepared.trajectory.movingFamily.patch label).boundary (start + elapsed) angle) := by
    rw [fieldIdentity]
    exact prepared.trajectory.movingFamily_material_equation_of_margin prepared.marginPositive
      (globalInside elapsed inside) (path.safe _ (timeRange elapsed inside)).le label angle
  have equation (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (target : Fin 4) :=
    (prepared.trajectory.movingFamily.dipoleConfiguration_hasDerivAt path.evolution (timeRange elapsed inside) index
      (fun _ => globalInside elapsed inside) (fun patch => material elapsed inside (finProdFinEquiv (index, patch))) target).scomp
        elapsed ((hasDerivAt_id elapsed).const_add start)
  have internalGap (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) (receiver source : Fin 4) (different : source ≠ receiver) :
      factor * length ≤ ‖patchCentroid motion (start + elapsed) index receiver - patchCentroid motion (start + elapsed) index source‖ := by
    have actual := path.internalClosed _ (timeRange elapsed inside) (index, receiver) (index, source)
    rw [cascadeInternalGapMonitor, if_pos (show (index, receiver).1 = (index, source).1 ∧
      (index, receiver).2 ≠ (index, source).2 from ⟨rfl, different.symm⟩)] at actual
    rw [prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside elapsed inside),
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) (globalInside elapsed inside)] at actual
    exact sub_nonpos.mp actual
  have residualControl (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖dipolePatchResidual changed motion (start + elapsed) index‖ ≤ (1 / 4096 : ℝ) * length := by
    have actual := path.evolution.dipolePatchResidual_bound (timeRange elapsed inside) amplitudePositive
      frequencyPositive ratioPositive index (cascadeForeignDistance changed factor index)
      (path.boundary _ (timeRange elapsed inside) index) (by positivity)
      (budgets.2 count index).1 (mul_pos factorPositive lengthPositive) (by
        change 8 * changed.radius (index.val + 1) ≤ factor * length
        have bound : changed.radius (index.val + 1) ≤ factor * length / 1000 := radiusInternal index
        have positive := mul_pos factorPositive lengthPositive
        linarith)
      (internalGap elapsed inside) (fun source member => (foreign elapsed inside source member).1)
      (fun source _ patch => sourceBounded elapsed inside source patch)
      (fun source member => (foreign elapsed inside source member).2.1)
      (fun source member => (foreign elapsed inside source member).2.2.1)
      (fun receiver source member => (foreign elapsed inside source member).2.2.2.1 receiver)
    exact actual.trans (budgets.2 count index).2
  have lipschitz (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :=
    path.evolution.externalPatch_biotSavart_lipschitzOn (timeRange elapsed inside) amplitudePositive frequencyPositive
      ratioPositive index (cascadeForeignDistance changed factor index) (region elapsed)
      (bound := (⟨1 / 4096, by norm_num⟩ : ℝ≥0))
      (fun source member => (foreign elapsed inside source member).1) (separated elapsed inside)
      ((changed.cascadeForeignStrain_le frequencyOne ratioBound alphaPositive factorPositive index).trans budgets.1)
  have actual := quadrupoleCenteredForcing_norm_le changed motion time index
    (region := region time) (strain := (⟨1 / 4096, by norm_num⟩ : ℝ≥0))
    (residualBound := (1 / 4096 : ℝ) * length)
    (by simpa only [start, zero_add] using lipschitz time inside)
    (fun patch => ⟨patch, by simp only [start, zero_add]⟩)
    (by simpa only [start, zero_add] using residualControl time inside)
  have scalar (first second : ℝ) :
      2 * (1 / 4096 : ℝ) * first + 2 * ((1 / 4096 : ℝ) * second) =
        (1 / 2048 : ℝ) * (first + second) := by ring
  exact actual.trans_eq (scalar _ _)

end EulerNonuniqueness.Paper

