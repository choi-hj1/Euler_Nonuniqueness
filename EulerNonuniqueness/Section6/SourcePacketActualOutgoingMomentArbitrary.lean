import EulerNonuniqueness.Section5.CascadePostHitScalarBudget
import EulerNonuniqueness.Section5.CascadeInternallyStoppedPath
import EulerNonuniqueness.Section5.CascadeMaterialForeignGeometry
import EulerNonuniqueness.Section7.PaperDipoleDynamics
import EulerNonuniqueness.Section6.SourcePacketMomentArbitraryBudget
import EulerNonuniqueness.Section6.MovingPatchWeightedMomentRamp
import EulerNonuniqueness.Section6.MovingExternalPatchField

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology NNReal BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem Scales.eventually_actual_outgoing_moment_arbitrary_budget (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1)
    (rootPositive : 0 < scaleRoot) (boundaryNonnegative : 0 ≤ boundaryConstant)
    {tolerance initialError : ℝ} (tolerancePositive : 0 < tolerance) (initialErrorSmall : initialError ≤ 1 / 64) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count,
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → horizon ≤ 1 →
    start + horizon ≤ path.stop → 2048 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency}).omega (index.val + 1) / 16 →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ tolerance / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := ({scales with frequency := frequency}).length (index.val + 1)
    let omega : ℝ := ({scales with frequency := frequency}).omega (index.val + 1)
    ‖firstDipoleSeparation motion start index - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start index - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start index - secondDipoleCenter motion start index)).re →
    ‖firstDipoleCenter motion start index - secondDipoleCenter motion start index‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    ∀ distance : ℝ, 0 < distance →
    let moment := fun time => ∫ position, quadrupoleDensity ({scales with frequency := frequency}) motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2
    (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 *
        ({scales with frequency := frequency}).omega index.val) * elapsed) *
        ‖moment (start + elapsed) - moment start -
          ({scales with frequency := frequency}).circulation (index.val + 1) •
            ((-4 * Complex.I * (omega : ℂ) * (length : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ))‖) ≤
      tolerance * (Real.sqrt 3 * ({scales with frequency := frequency}).circulation (index.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * ({scales with frequency := frequency}).omega index.val ^ 2 * distance ^ 4)) := by
  let errorBudget := min (1 / 16384 : ℝ) (tolerance / 10000)
  have errorPositive : 0 < errorBudget := by dsimp only [errorBudget]; positivity
  have fifthLimit : Tendsto (fun frequency : ℝ => (2 * boundaryConstant / (scales.amplitude * scaleRoot ^ 2)) * frequency⁻¹ ^ 5)
      atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (5 : ℕ) ≠ 0), mul_zero] using
      ((tendsto_inv_atTop_zero : Tendsto (fun frequency : ℝ => frequency⁻¹) atTop (𝓝 0)).pow 5).const_mul
        (2 * boundaryConstant / (scales.amplitude * scaleRoot ^ 2))
  filter_upwards [eventually_ge_atTop (64 : ℝ),
    scales.eventually_cascade_posthit_scalar_budgets amplitudePositive (by linarith : 2 ≤ scales.ratio) alphaPositive
      factorPositive rootPositive boundaryNonnegative errorPositive,
    scales.eventually_cascade_geometric_scale_smallness amplitudePositive (by linarith : 2 ≤ scales.ratio) alphaPositive
      factorPositive factorSmall (by norm_num : (3 : ℝ) ≤ 3),
    fifthLimit.eventually (eventually_lt_nhds (show (0 : ℝ) < tolerance / 6144 by positivity))]
    with frequency frequencyLarge budgets geometry fifthSmall
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path index start horizon initialDistance
    startNonnegative horizonNonnegative horizonUpper endBound initialDistanceLarge initialDistanceSmall initialNumeric direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper distance distancePositive
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
      ‖dipolePatchResidual changed motion (start + elapsed) index‖ ≤ (errorBudget : ℝ) * length := by
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
      (bound := (⟨errorBudget, errorPositive.le⟩ : ℝ≥0))
      (fun source member => (foreign elapsed inside source member).1) (separated elapsed inside)
      ((changed.cascadeForeignStrain_le frequencyOne (by linarith : 2 ≤ scales.ratio) alphaPositive factorPositive index).trans budgets.1)

  have configuration (elapsed : ℝ) :
      relabelNegativePoints (fun patch => patchCentroid motion (start + elapsed) index patch) =
        twoDipoleConfiguration (firstDipoleCenter motion (start + elapsed) index)
          (secondDipoleCenter motion (start + elapsed) index)
          (firstDipoleSeparation motion (start + elapsed) index)
          (secondDipoleSeparation motion (start + elapsed) index) := by
    funext patch
    rw [twoDipoleConfiguration_patchCentroids]
    fin_cases patch <;> rfl
  have residualUnpermuted (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖fun patch => quadrupoleInternalPatchResidual changed motion (start + elapsed) index patch +
        quadrupoleExternalReceiverResidual changed motion (start + elapsed) index patch‖ ≤
          (errorBudget : ℝ) * length := by
    have identity : dipolePatchResidual changed motion (start + elapsed) index =
        relabelNegativePoints (fun patch => quadrupoleInternalPatchResidual changed motion (start + elapsed) index patch +
          quadrupoleExternalReceiverResidual changed motion (start + elapsed) index patch) := by
      funext patch
      fin_cases patch <;> rfl
    have actual := residualControl elapsed inside
    rwa [identity, relabelNegativePoints_norm] at actual
  have radiusSmall : changed.radius (index.val + 1) ≤ length := by
    have bound := radiusInternal index
    have scaled := mul_le_of_le_one_left lengthPositive.le factorSmall
    linarith
  have ratioDistance : initialDistance / omega ≤ 1 / 16 :=
    (div_le_iff₀ omegaPositive).mpr (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using initialDistanceSmall)
  have errorSmall : errorBudget ≤ 1 / 16384 := min_le_left _ _
  have errorTolerance : 2 * errorBudget ≤ tolerance / 5000 := by
    have bound : errorBudget ≤ tolerance / 10000 := min_le_right _ _
    linarith
  have omegaPositive : 0 < omega := by linarith
  have inverseBound : 1 / omega ≤ 1 := (div_le_one omegaPositive).mpr (by linarith)
  have centerRaw : 8 * errorBudget * (horizon + initialDistance / omega) + 2 * errorBudget / omega ≤ 1 / 2 := by
    have inverseScaled := mul_le_mul_of_nonneg_left inverseBound (show 0 ≤ 2 * errorBudget by positivity)
    simp only [mul_one, ← mul_div_assoc, mul_one_div] at inverseScaled
    nlinarith
  have weighted := prepared.trajectory.movingFamily.quadrupole_literal_moment_weighted_ramp path.evolution
    amplitudePositive frequencyPositive ratioPositive index configuration horizonNonnegative timeRange
    (fun elapsed inside _ => globalInside elapsed inside)
    (fun elapsed inside patch => material elapsed inside (finProdFinEquiv (index, patch))) lipschitz
    (by intro elapsed inside patch; rw [twoDipoleConfiguration_patchCentroids]; exact ⟨dipolePatchPermutation patch, rfl⟩)
    residualUnpermuted directionNorm (by linarith : 512 ≤ initialDistance) initialErrorSmall errorPositive.le
    (by change 64 * (errorBudget + errorBudget) * horizon ≤ 1; nlinarith)
    (by simpa only [NNReal.coe_mk] using centerRaw)
    (by simpa only [add_zero] using firstInitial) (by simpa only [add_zero] using secondInitial)
    (by simpa only [add_zero] using initialProjection) (by simpa only [add_zero] using initialUpper)
    (fun elapsed inside => path.boundary _ (timeRange elapsed inside) index) (by positivity) (budgets.2 count index).1
    (show 0 < 2 * Real.sqrt 2 * changed.omega index.val by
      exact mul_pos (by positivity) (changed.omega_pos frequencyPositive ratioPositive index.val))
  have numeric : 20 * initialError + 83200 / initialDistance ^ 2 +
      76 * (errorBudget + errorBudget) * horizon +
      36 * (errorBudget + errorBudget) * initialDistance / omega ≤ tolerance / 4 := by
    have timeBound := mul_le_mul_of_nonneg_left horizonUpper (show 0 ≤ 2 * errorBudget by positivity)
    have centerBound := mul_le_mul_of_nonneg_left ratioDistance (show 0 ≤ 2 * errorBudget by positivity)
    have centerNormalized : (2 * errorBudget) * initialDistance / omega ≤ 2 * errorBudget := by
      have comparison : initialDistance / omega ≤ 1 := ratioDistance.trans (by norm_num)
      simpa only [mul_one, mul_div_assoc] using mul_le_mul_of_nonneg_left comparison (show 0 ≤ 2 * errorBudget by positivity)
    rw [show 36 * (errorBudget + errorBudget) * initialDistance / omega =
      36 * ((2 * errorBudget) * initialDistance / omega) by ring]
    nlinarith
  have coefficientNonnegative : 0 ≤ 2 * boundaryConstant / (changed.amplitude * scaleRoot ^ 2) := by positivity
  have inversePower := pow_le_pow_left₀ (inv_nonneg.mpr omegaPositive.le)
    (inv_anti₀ frequencyPositive (changed.omega_ge_frequency frequencyPositive (by linarith) (index.val + 1))) 5
  have fineSmall := (mul_le_mul_of_nonneg_left inversePower coefficientNonnegative).trans fifthSmall.le
  have deformationNumeric : changed.radius (index.val + 1) ^ 2 * deformation ≤
      tolerance * changed.length (index.val + 1) ^ 2 / 6144 := by
    have identity : changed.radius (index.val + 1) ^ 2 * deformation =
        changed.length (index.val + 1) ^ 2 *
          ((2 * boundaryConstant / (changed.amplitude * scaleRoot ^ 2)) * omega⁻¹ ^ 5) := by
      rw [changed.radius_sq amplitudePositive frequencyPositive ratioPositive]
      dsimp only [deformation, omega]
      field_simp [amplitudePositive.ne', rootPositive.ne', omegaPositive.ne']
      <;> ring
    rw [identity]
    convert mul_le_mul_of_nonneg_left fineSmall (sq_nonneg (changed.length (index.val + 1))) using 1 <;> ring
  have scalar := changed.moment_ramp_weighted_arbitrary_cost index.val frequencyPositive ratioPositive distancePositive
    (by change 1 ≤ scales.ratio; linarith) tolerancePositive numeric deformationNumeric
  have multiplied := mul_le_mul_of_nonneg_left weighted (show 0 ≤ 6 / (Real.pi * distance ^ 4) by positivity)
  exact multiplied.trans scalar

end EulerNonuniqueness.Paper

