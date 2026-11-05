import EulerNonuniqueness.Section5.CascadePostHitScalarBudget
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section5.CascadeMaterialForeignGeometry
import EulerNonuniqueness.Section7.PaperDipoleDynamics
import EulerNonuniqueness.Section7.PostHitAnnulus
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set Metric Filter
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_material_posthit_comoving_annulus (scales : Scales)
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
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 1 / 2 ≤ horizon → horizon ≤ 1 →
    start + horizon ≤ path.stop → 512 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency}).omega (index.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := ({scales with frequency := frequency}).length (index.val + 1)
    let omega : ℝ := ({scales with frequency := frequency}).omega (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ patch position, position ∈ motion.domain (start + horizon) index patch →
      omega * length / 16 ≤
        ‖position - (firstDipoleCenter motion (start + horizon) index + secondDipoleCenter motion (start + horizon) index) / 2‖ ∧
      ‖position - (firstDipoleCenter motion (start + horizon) index + secondDipoleCenter motion (start + horizon) index) / 2‖ ≤
        2 * omega * length := by
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive ratioBound alphaPositive
      factorPositive rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1 / 4096),
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive ratioBound alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3)]
    with frequency frequencyLarge budgets geometry
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start horizon initialDistance
    startNonnegative horizonLower horizonUpper endBound initialDistanceLarge initialDistanceSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper
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
  have horizonNonnegative : 0 ≤ horizon := by linarith
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
  have continuation := twoDipole_forced_continued_separation
    (firstCenter := fun elapsed => firstDipoleCenter motion (start + elapsed) index)
    (secondCenter := fun elapsed => secondDipoleCenter motion (start + elapsed) index)
    (firstSeparation := fun elapsed => firstDipoleSeparation motion (start + elapsed) index)
    (secondSeparation := fun elapsed => secondDipoleSeparation motion (start + elapsed) index)
    (external := fun elapsed => biotSavart (externalPatchVorticity changed motion (start + elapsed) index))
    (residual := fun elapsed => dipolePatchResidual changed motion (start + elapsed) index)
    (region := region) (strain := (⟨1 / 4096, by norm_num⟩ : ℝ≥0)) omegaPositive lengthPositive directionNorm
    initialDistanceLarge horizonNonnegative (by norm_num : (0 : ℝ) ≤ 1 / 4096)
    (by norm_num; linarith)
    (by
      change 8 * (1 / 4096 : ℝ) * (horizon + initialDistance / omega) + 2 * (1 / 4096 : ℝ) / omega ≤ 1 / 2
      have ratioBounded : initialDistance / omega ≤ 1 / 16 := (div_le_iff₀ omegaPositive).mpr (by linarith)
      have inverseBound : 1 / omega ≤ 1 := (div_le_one omegaPositive).mpr (by linarith)
      have inverseScaled : 2 * (1 / 4096 : ℝ) / omega ≤ 2 * (1 / 4096 : ℝ) := by
        simpa only [mul_one, mul_one_div] using mul_le_mul_of_nonneg_left inverseBound
          (by norm_num : (0 : ℝ) ≤ 2 * (1 / 4096 : ℝ))
      linarith)
    (by simpa only [Function.comp_def, one_smul] using equation) lipschitz
    (by intro elapsed inside target; rw [twoDipoleConfiguration_patchCentroids]; exact ⟨dipolePatchPermutation target, rfl⟩)
    residualControl (by simpa using firstInitial) (by simpa using secondInitial)
    (by simpa using initialProjection) (by simpa using initialUpper)
  have endInside : horizon ∈ Icc 0 horizon := ⟨horizonNonnegative, le_rfl⟩
  have endControl := continuation horizon endInside
  have firstBound := (dipole_separation_norm_bounds length lengthPositive directionNorm endControl.1).2
  have secondBound := (dipole_separation_norm_bounds length lengthPositive
    (show ‖-direction‖ = 1 by simpa using directionNorm) endControl.2.1).2
  have domainControl (target : Fin 4) : motion.domain (start + horizon) index (dipolePatchPermutation target) ⊆
      closedBall (twoDipoleConfiguration (firstDipoleCenter motion (start + horizon) index)
        (secondDipoleCenter motion (start + horizon) index) (firstDipoleSeparation motion (start + horizon) index)
        (secondDipoleSeparation motion (start + horizon) index) target) (2 * changed.radius (index.val + 1)) := by
    rw [twoDipoleConfiguration_patchCentroids]
    exact sourceBounded horizon endInside index _
  intro patch position member
  have actual := EulerNonuniqueness.Section7.twoDipole_domain_annular_estimate firstBound secondBound
    (centerError := 0) (by rw [sub_self, norm_zero]) domainControl (dipolePatchPermutation.symm patch) position
    (by simpa only [Equiv.apply_symm_apply] using member)
  have radiusBound : 2 * changed.radius (index.val + 1) ≤ length := by
    have factorBound := mul_le_of_le_one_left lengthPositive.le factorSmall
    linarith [radiusInternal index]
  have lowerProduct := mul_le_mul_of_nonneg_left horizonLower (mul_nonneg omegaPositive.le lengthPositive.le)
  have upperProduct := mul_le_mul_of_nonneg_left horizonUpper (mul_nonneg omegaPositive.le lengthPositive.le)
  have initialProduct := mul_le_mul_of_nonneg_left initialDistanceSmall lengthPositive.le
  have largeProduct := mul_le_mul_of_nonneg_right omegaLarge lengthPositive.le
  constructor <;> nlinarith [actual.1, actual.2, endControl.2.2.1, endControl.2.2.2]

end EulerNonuniqueness.Paper
