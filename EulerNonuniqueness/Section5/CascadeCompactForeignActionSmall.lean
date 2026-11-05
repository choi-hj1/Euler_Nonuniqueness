import EulerNonuniqueness.Section5.CascadeActualMacroForeignVelocityAction
import EulerNonuniqueness.Section5.CascadeExtentMacroSourceStateBound
import EulerNonuniqueness.Section5.CascadeExternalVelocityContinuity
import EulerNonuniqueness.Section4.QuadrupoleCenterNormBound

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem omega_location_four_lower {scales : Scales}
    (frequencyNonnegative : 0 ≤ scales.frequency) (ratioLarge : 16 ≤ scales.ratio) (index : ℕ) :
    scales.frequency ≤ scales.omega index * scales.location index ^ 4 := by
  have powers : (16 : ℝ) ^ index ≤ scales.ratio ^ index := pow_le_pow_left₀ (by norm_num) ratioLarge _
  have positive : 0 < (16 : ℝ) ^ index := by positivity
  have location : scales.location index ^ 4 = ((16 : ℝ) ^ index)⁻¹ := by
    rw [scales.location_eq_inv_pow, inv_pow, ← pow_mul, Nat.mul_comm index 4, pow_mul]
    norm_num
  rw [Scales.omega, location]
  have lower := mul_le_mul_of_nonneg_right powers (inv_nonneg.mpr positive.le)
  rw [mul_inv_cancel₀ positive.ne'] at lower
  have scaled := mul_le_mul_of_nonneg_left lower frequencyNonnegative
  simpa only [mul_one, mul_assoc] using scaled

theorem exists_uniform_actual_compact_foreign_action_small :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∀ span ≥ (0 : ℝ), ∀ scales : Scales,
    0 < scales.amplitude → 16 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let omega := changed.omega (index.val + 1)
    let location := changed.location (index.val + 1)
    let foreign := fun time => (∑ patch : Fin 4,
      ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
        biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * location)
    ContinuousOn foreign (Icc 0 path.stop) ∧
    ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
      omega * (finish - start) ≤ span →
      IntervalIntegrable (fun time => Real.exp (-omega * (time - start)) * foreign time) volume start finish ∧
      (∫ time in start..finish, Real.exp (-omega * (time - start)) * foreign time) ≤ 1 := by
  obtain ⟨_, _, velocityCap, velocityCapPositive, velocityConstant, velocityNonnegative, velocities⟩ :=
    exists_uniform_actual_macro_foreign_velocity_action
  obtain ⟨shapeCap, shapeCapPositive, rawConstant, rawNonnegative, _, shapes⟩ :=
    exists_uniform_actual_extent_macro_source_state_bound
  let rawCap := min velocityCap shapeCap
  have velocityCapBound : rawCap ≤ velocityCap := min_le_left _ _
  have shapeCapBound : rawCap ≤ shapeCap := min_le_right _ _
  refine ⟨rawCap, lt_min velocityCapPositive shapeCapPositive, ?_⟩
  intro factor factorPositive factorSmall span spanNonnegative scales amplitudePositive ratioLarge alphaPositive
    orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
  have ratioBound : 2 ≤ scales.ratio := (by norm_num : (2 : ℝ) ≤ 16).trans ratioLarge
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  let constant := 50000 * (velocityConstant + 1) * (72 + rawConstant)
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  let rho := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency} : Scales).hessian +
    576 * ({scales with frequency := frequency} : Scales).strain
  have rhoLimit : Tendsto rho atTop (𝓝 0) := by
    simpa only [rho, mul_zero, zero_add] using
      ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  filter_upwards [velocities scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_patch_external_velocity_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    rhoLimit.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (constant * span + 1)] with frequency velocity continuous rhoSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let location := changed.location (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let foreign := fun time => (∑ patch : Fin 4,
    ‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
      biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖) / (4 * location)
  have frequencyPositive : 0 < frequency := by linarith only [frequencyLarge, mul_nonneg constantNonnegative spanNonnegative]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive (by linarith only [ratioBound]) _
  have locationPositive : 0 < location := changed.location_pos _
  have rawInvariant : (prepared.enlargeCap shapeCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have macroInvariant : (prepared.enlargeCap velocityCapBound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have macroBound (time : ℝ) (inside : time ∈ Icc 0 path.stop) (source : Fin count) :
      changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source ≤ 72 + rawConstant := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
    have centroidBound (side : Fin 2) (patch : Fin 4) :
        ‖patchCentroid (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time source patch‖ ≤ 4 := by
      fin_cases side
      · change ‖patchCentroid first time source patch‖ ≤ 4
        rw [← prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
        change ‖prepared.trajectory.center (finProdFinEquiv (source, patch)) time‖ ≤ 4
        rw [prepared.trajectory.center_eq_curve globalInside]
        exact (prepared.trajectory.admissible time).1 (finProdFinEquiv (source, patch))
      · change ‖patchCentroid prepared.reference time source patch‖ ≤ 4
        rw [prepared.referenceIdentity, ← prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
        change ‖prepared.referenceWitness.trajectory.center (finProdFinEquiv (source, patch)) time‖ ≤ 4
        rw [prepared.referenceWitness.trajectory.center_eq_curve globalInside]
        exact (prepared.referenceWitness.trajectory.admissible time).1 (finProdFinEquiv (source, patch))
    have firstCenter : ‖quadrupoleCenter first time source‖ ≤ 4 :=
      quadrupoleCenter_norm_le_of_patchCentroid_norm_le first time source (centroidBound 0)
    have secondCenter : ‖quadrupoleCenter second time source‖ ≤ 4 := by
      apply quadrupoleCenter_norm_le_of_patchCentroid_norm_le second time source
      intro patch
      have bound := centroidBound 1 patch
      change ‖patchCentroid prepared.reference time source patch‖ ≤ 4 at bound
      simpa only [prepared.referenceIdentity] using bound
    have centerDifference : ‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ ≤ 8 :=
      (norm_sub_le _ _).trans (by linarith only [firstCenter, secondCenter])
    have centeredDifference (patch : Fin 4) :
        ‖(patchCentroid second time source patch - quadrupoleCenter second time source) -
          (patchCentroid first time source patch - quadrupoleCenter first time source)‖ ≤ 16 := by
      have firstPatch : ‖patchCentroid first time source patch‖ ≤ 4 := centroidBound 0 patch
      have secondPatch : ‖patchCentroid second time source patch‖ ≤ 4 := by
        have bound := centroidBound 1 patch
        change ‖patchCentroid prepared.reference time source patch‖ ≤ 4 at bound
        simpa only [prepared.referenceIdentity] using bound
      have secondOffset := norm_sub_le (patchCentroid second time source patch) (quadrupoleCenter second time source)
      have firstOffset := norm_sub_le (patchCentroid first time source patch) (quadrupoleCenter first time source)
      exact (norm_sub_le _ _).trans (by linarith only [secondOffset, firstOffset, firstPatch, secondPatch, firstCenter, secondCenter])
    have rawBound := (shapes 0 le_rfl (prepared.enlargeCap shapeCapBound) path time inside source).1
    rw [rawInvariant] at rawBound
    have sumBound := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => centeredDifference patch)
    norm_num only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at sumBound
    have positive := changed.location_pos (source.val + 1)
    have macroEstimate : prepared.macroSourceState time source ≤ 72 / changed.location (source.val + 1) + rawConstant := by
      have identity : prepared.macroSourceState time source =
          (‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ +
            ∑ patch : Fin 4,
              ‖(prepared.referenceWitness.trajectory.movingFamily.cascadeCenters time (source, patch) - quadrupoleCenter second time source) -
                (prepared.trajectory.movingFamily.cascadeCenters time (source, patch) - quadrupoleCenter first time source)‖) /
              changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
        with_reducible_and_instances
          dsimp only [CascadeSourcePreparedPair.macroSourceState, CascadeSourcePreparedPair.rawSourceShapeBudget,
            MovingCentroidGaugeTrajectory.spectralCoordinate, first, second, changed]
      rw [identity]
      simp_rw [prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside,
        prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside]
      have numerator : ‖quadrupoleCenter second time source - quadrupoleCenter first time source‖ +
          (∑ patch : Fin 4, ‖(patchCentroid second time source patch - quadrupoleCenter second time source) -
            (patchCentroid first time source patch - quadrupoleCenter first time source)‖) ≤ 72 := by linarith only [centerDifference, sumBound]
      have divided := div_le_div_of_nonneg_right numerator positive.le
      exact add_le_add divided rawBound
    have locationOne := changed.location_le_one (source.val + 1)
    calc
      _ ≤ changed.location (source.val + 1) ^ 4 * (72 / changed.location (source.val + 1) + rawConstant) :=
        mul_le_mul_of_nonneg_left macroEstimate (pow_nonneg positive.le 4)
      _ = 72 * changed.location (source.val + 1) ^ 3 + rawConstant * changed.location (source.val + 1) ^ 4 := by
        field_simp; ring
      _ ≤ 72 + rawConstant := by
        have third : changed.location (source.val + 1) ^ 3 ≤ 1 := pow_le_one₀ positive.le locationOne
        have fourth : changed.location (source.val + 1) ^ 4 ≤ 1 := pow_le_one₀ positive.le locationOne
        nlinarith only [third, mul_le_mul_of_nonneg_left fourth rawNonnegative]
  have globalMacro (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ ≤ 72 + rawConstant := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro source
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (changed.location_pos _).le 4)
      (prepared.macroSourceState_nonnegative time source))]
    exact macroBound time inside source
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 path.stop) : location ^ 4 * foreign time ≤ constant := by
    have each (patch : Fin 4) : location ^ 4 *
        (‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
          biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖ / location) ≤ constant := by
      obtain ⟨_, bound⟩ := velocity count phase dipoleAngle (prepared.enlargeCap velocityCapBound) path inside (index, patch)
      simp only [macroInvariant] at bound
      with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at bound
      have rhoNonnegative : 0 ≤ rho frequency := by
        have hessian : 0 ≤ changed.hessian := tsum_nonneg (fun source => div_nonneg
          (changed.circulation_pos frequencyPositive (by linarith only [ratioBound]) _).le (pow_nonneg (changed.location_pos _).le 3))
        have strain : 0 ≤ changed.strain := tsum_nonneg (fun source => div_nonneg
          (changed.circulation_pos frequencyPositive (by linarith only [ratioBound]) _).le (sq_nonneg (changed.location _)))
        change 0 ≤ 216360000 * changed.hessian + 576 * changed.strain
        positivity
      have upper := mul_le_mul_of_nonneg_left (globalMacro time inside)
        (show 0 ≤ 50000 * (velocityConstant + 1) * rho frequency by positivity)
      have bounded := (mul_le_mul_of_nonneg_left rhoSmall.le (by positivity : 0 ≤ 50000 * (velocityConstant + 1))).trans_eq (mul_one _)
      have final := mul_le_mul_of_nonneg_right bounded (show 0 ≤ 72 + rawConstant by positivity)
      rw [norm_sub_rev] at bound
      apply (show _ ≤ _ from bound).trans
      simpa only [constant, rho, mul_assoc, norm_sub_rev] using upper.trans final
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => each patch)
    have identity : (∑ patch : Fin 4, location ^ 4 *
        (‖biotSavart (externalPatchVorticity changed first time index) (patchCentroid first time index patch) -
          biotSavart (externalPatchVorticity changed second time index) (patchCentroid second time index patch)‖ / location)) =
        4 * (location ^ 4 * foreign time) := by
      dsimp only [foreign]
      simp_rw [← mul_div_assoc]
      rw [← Finset.sum_div, ← Finset.mul_sum]
      field_simp; ring
    rw [identity] at summed
    norm_num only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at summed
    linarith only [summed]
  have foreignContinuous : ContinuousOn foreign (Icc 0 path.stop) := by
    apply ContinuousOn.div_const
    apply continuousOn_finset_sum
    intro patch _
    exact (continuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index patch).norm
  refine ⟨foreignContinuous, ?_⟩
  intro start startInside finish finishInside spanBound
  have subset : Icc start finish ⊆ Icc 0 path.stop := Icc_subset_Icc startInside.1 finishInside.2
  have weightedContinuous := (show Continuous (fun time : ℝ => Real.exp (-omega * (time - start))) by fun_prop).continuousOn.mul
    (foreignContinuous.mono subset)
  have weightedI := weightedContinuous.intervalIntegrable_of_Icc (μ := volume) finishInside.1
  refine ⟨weightedI, ?_⟩
  have comparison := intervalIntegral.integral_mono_on finishInside.1 weightedI
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => constant / location ^ 4) volume start finish) (by
      intro time inside
      have nonnegative : 0 ≤ foreign time := by dsimp only [foreign]; positivity
      have exponential : Real.exp (-omega * (time - start)) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr omegaPositive.le) (sub_nonneg.mpr inside.1)
      have fieldBound : foreign time ≤ constant / location ^ 4 := (le_div_iff₀ (pow_pos locationPositive 4)).mpr (by
        simpa only [mul_comm] using pointwise time (subset inside))
      exact (mul_le_of_le_one_left nonnegative exponential).trans fieldBound)
  rw [intervalIntegral.integral_const, smul_eq_mul] at comparison
  have frequencyLower : frequency ≤ omega * location ^ 4 := omega_location_four_lower (scales := changed) frequencyPositive.le ratioLarge _
  have duration := mul_le_mul_of_nonneg_right frequencyLower (sub_nonneg.mpr finishInside.1)
  have positiveLocation := pow_pos locationPositive 4
  have scaled := mul_le_mul_of_nonneg_right spanBound positiveLocation.le
  have timeProduct : frequency * (finish - start) ≤ span * location ^ 4 := by
    nlinarith only [duration, scaled]
  have target : (finish - start) * (constant / location ^ 4) ≤ 1 := by
    have ratio : constant * (finish - start) ≤ location ^ 4 := by
      have product := mul_le_mul_of_nonneg_left timeProduct constantNonnegative
      have small := mul_le_mul_of_nonneg_right (show constant * span ≤ frequency by linarith only [frequencyLarge]) positiveLocation.le
      apply (mul_le_mul_left frequencyPositive).mp
      nlinarith only [product, small]
    calc
      _ = (constant * (finish - start)) / location ^ 4 := by ring
      _ ≤ 1 := (div_le_one positiveLocation).mpr ratio
  exact comparison.trans target

end EulerNonuniqueness.Paper
