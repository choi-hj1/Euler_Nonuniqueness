import EulerNonuniqueness.Section5.CascadeCoarserVelocityMacroFeedback
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section6.SourcePacketActualPrehitPatchVelocityBudget
import EulerNonuniqueness.Section6.SourcePacketFinerPatchVelocitySeedTail
import EulerNonuniqueness.Section6.MovingForeignVelocitySum
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability
import EulerNonuniqueness.General.ErasedAdjacentSum

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem quadrupole_vorticity_actual_density {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    (source : Fin count) (time : ℝ) :
    (family.quadrupoleSubfamily source).vorticity time = quadrupoleDensity scales family.patchMotion time source := by
  funext position
  apply Finset.sum_congr rfl
  intro patch _
  change ((family.patch (finProdFinEquiv (source, patch))).domain time).indicator
    (fun _ => family.density (finProdFinEquiv (source, patch))) position = _
  rw [densities]
  rfl

private theorem adjacent_velocity_distance_normalization
    {value receiverDistance sourceDistance : ℝ}
    (sourcePositive : 0 < sourceDistance) (identity : receiverDistance = 2 * sourceDistance) :
    value / receiverDistance = (1 / 2 : ℝ) * (value / sourceDistance) := by
  rw [identity]
  field_simp [sourcePositive.ne']

theorem exists_uniform_actual_driven_patch_velocity_window_return :
    ∃ rawCap > (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∃ coarserConstant ≥ (0 : ℝ), ∃ packetConstant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 8192 ≤ scales.ratio → 0 < scales.alpha →
    4 < scales.ratio ^ scales.alpha → ∀ tolerance > (0 : ℝ),
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant → 0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon initialDistance outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio → 20 * initialError + 83200 / initialDistance ^ 2 ≤ 1 / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    (∀ time ∈ Icc 0 (start + horizon), |radialShape motion time receiver| ≤ 1 / 2) →
    ∀ patch : Fin 4,
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let decay := 2 * Real.sqrt 2 * changed.omega source.val
    let field := fun elapsed =>
      biotSavart (externalPatchVorticity changed motion (start + elapsed) receiver)
          (patchCentroid motion (start + elapsed) receiver patch) -
        biotSavart (externalPatchVorticity changed reference (start + elapsed) receiver)
          (patchCentroid reference (start + elapsed) receiver patch)
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (‖field elapsed‖ / changed.location (receiver.val + 1))) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      (‖field elapsed‖ / changed.location (receiver.val + 1))) ≤
      (coarserConstant / changed.location (receiver.val + 1) ^ 4) *
        (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
          ‖fun index : Fin count => if index.val ≤ receiver.val then
            changed.location (index.val + 1) ^ 4 * prepared.macroSourceState (start + elapsed) index else 0‖) +
      packetConstant * changed.seed (receiver.val + 1) + tolerance * changed.seed (receiver.val + 1) / decay := by
  obtain ⟨coarserCap, coarserPositive, coarserConstant, coarserNonnegative, coarserFactory⟩ :=
    exists_uniform_actual_coarser_velocity_macro_feedback
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨radius, radiusPositive, radiusSmall, packetBase, packetNonnegative, packetFactory⟩ :=
    exists_actual_prehit_patch_source_velocity_seed_budget
  let rawCap := min coarserCap continuityCap
  have capPositive : 0 < rawCap := lt_min coarserPositive continuityPositive
  refine ⟨rawCap, capPositive, radius, radiusPositive, radiusSmall, coarserConstant, coarserNonnegative,
    packetBase / 2, div_nonneg packetNonnegative (by norm_num), ?_⟩
  intro scales amplitudePositive ratioLarge alphaPositive ratioPower tolerance tolerancePositive referenceConstant
    referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := by linarith only [ratioLarge]
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [coarserFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_actual_finer_patch_velocity_seed_tail amplitudePositive ratioBound alphaPositive ratioPower
      tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    packetFactory scales amplitudePositive ratioLarge alphaPositive referenceConstant referenceNonnegative amplitudeBound
      threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive
      factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency coarser finer packet frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prehistory radialSmall patch
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let decay := 2 * Real.sqrt 2 * changed.omega source.val
  let velocity := fun index elapsed =>
    biotSavart (quadrupoleDensity changed first.patchMotion (start + elapsed) index)
        (patchCentroid first.patchMotion (start + elapsed) receiver patch) -
      biotSavart (quadrupoleDensity changed second.patchMotion (start + elapsed) index)
        (patchCentroid second.patchMotion (start + elapsed) receiver patch)
  let field := fun elapsed =>
    biotSavart (externalPatchVorticity changed first.patchMotion (start + elapsed) receiver)
        (patchCentroid first.patchMotion (start + elapsed) receiver patch) -
      biotSavart (externalPatchVorticity changed second.patchMotion (start + elapsed) receiver)
        (patchCentroid second.patchMotion (start + elapsed) receiver patch)
  let error := fun elapsed => ‖field elapsed‖ / changed.location (receiver.val + 1)
  let adjacentError := fun elapsed => ‖velocity source elapsed‖ / changed.location (receiver.val + 1)
  let maskedState := fun elapsed => ‖fun index : Fin count => if index.val ≤ receiver.val then
    changed.location (index.val + 1) ^ 4 * prepared.macroSourceState (start + elapsed) index else 0‖
  let coefficient := (coarserConstant / changed.location (receiver.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  let remainder := tolerance * changed.seed (receiver.val + 1)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioLarge]
  have decayPositive : 0 < decay := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive source.val
    dsimp only [decay]
    positivity
  have locationPositive := changed.location_pos (receiver.val + 1)
  have sourceDistancePositive := changed.location_pos (source.val + 1)
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [inside.2, endBound]⟩
  have distanceIdentity : changed.location (receiver.val + 1) = 2 * changed.location (source.val + 1) := by
    rw [← adjacent, changed.location_eq_inv_pow, changed.location_eq_inv_pow, pow_succ]
    field_simp
    ring
  have fieldIdentity (elapsed : ℝ) : field elapsed = ∑ index ∈ Finset.univ.erase receiver, velocity index elapsed := by
    dsimp only [field, velocity]
    rw [first.externalPatch_biotSavart_eq_sum_quadrupoles changed prepared.densityIdentity,
      second.externalPatch_biotSavart_eq_sum_quadrupoles changed prepared.referenceWitness.densityIdentity]
    simp_rw [quadrupole_vorticity_actual_density first changed prepared.densityIdentity,
      quadrupole_vorticity_actual_density second changed prepared.referenceWitness.densityIdentity]
    rw [Finset.sum_sub_distrib]
  have fieldMeasurable (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ index patch, family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * changed.amplitude * changed.omega (index.val + 1) ^ 4) (index : Fin count) :
      Measurable (fun time => biotSavart (quadrupoleDensity changed family.patchMotion time index)
        (patchCentroid family.patchMotion time receiver patch)) := by
    have joint : Measurable (fun point : ℝ × ℂ => biotSavart
        (quadrupoleDensity changed family.patchMotion point.1 index) point.2) :=
      measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => quadrupoleDensity changed family.patchMotion time index)
      (family.measurable_quadrupoleDensity changed densities index)
    have locations := (family.patchCentroid_continuous receiver patch).measurable
    have parameterMeasurable : Measurable (fun time : ℝ =>
        (time, patchCentroid family.patchMotion time receiver patch)) := measurable_id.prodMk locations
    with_reducible_and_instances
      simpa only [Function.comp_def] using joint.comp parameterMeasurable
  have velocityMeasurable (index : Fin count) : Measurable (velocity index) := by
    have shiftedMeasurable : Measurable (fun elapsed : ℝ => start + elapsed) := measurable_const.add measurable_id
    have actual := ((fieldMeasurable first prepared.densityIdentity index).sub
      (fieldMeasurable second prepared.referenceWitness.densityIdentity index)).comp shiftedMeasurable
    simpa only [velocity, Function.comp_def] using actual
  have errorMeasurable : Measurable error := by
    have identity : error = fun elapsed => ‖∑ index ∈ Finset.univ.erase receiver, velocity index elapsed‖ /
        changed.location (receiver.val + 1) := by
      funext elapsed
      dsimp only [error]
      rw [fieldIdentity]
    rw [identity]
    exact (Finset.measurable_sum _ (fun index _ => velocityMeasurable index)).norm.div_const _
  let enlarged := prepared.enlargeCap (min_le_left coarserCap continuityCap)
  have coarse (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      (∑ index ∈ Finset.univ.filter (fun index : Fin count => index.val < receiver.val), ‖velocity index elapsed‖) /
        changed.location (receiver.val + 1) ≤ coefficient * maskedState elapsed := by
    have actual := coarser count phase dipoleAngle enlarged path (start + elapsed) (timeRange elapsed inside) (receiver, patch)
    with_reducible_and_instances
      dsimp only [velocity, coefficient, maskedState, changed, first, second, CascadeSourcePreparedPair.macroSourceState,
        enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
      rw [prepared.referenceIdentity] at actual
      exact actual
  have fine (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      (∑ index ∈ Finset.univ.filter (fun index : Fin count => receiver.val + 2 ≤ index.val), ‖velocity index elapsed‖) /
        changed.location (receiver.val + 1) ≤ remainder := by
    have actual := finer count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path (start + elapsed)
      (timeRange elapsed inside) (receiver, patch)
    simpa only [velocity, remainder, first, second, prepared.referenceIdentity] using actual
  obtain ⟨adjacentIntegrableSource, adjacentBoundSource⟩ :=
    packet count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source adjacent start horizon
      initialDistance outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall
      ratioBudget initialBudget firstInitial secondInitial initialProjection initialUpper prehistory radialSmall patch
  have weightedAdjacentIdentity (elapsed : ℝ) : Real.exp (-decay * elapsed) * adjacentError elapsed =
      (1 / 2 : ℝ) * (Real.exp (-decay * elapsed) * ‖velocity source elapsed‖ / changed.location (source.val + 1)) := by
    dsimp only [adjacentError]
    rw [← mul_div_assoc]
    exact adjacent_velocity_distance_normalization sourceDistancePositive distanceIdentity
  have adjacentIntegrable : IntervalIntegrable
      (fun elapsed => Real.exp (-decay * elapsed) * adjacentError elapsed) volume 0 horizon := by
    simpa only [weightedAdjacentIdentity, velocity] using adjacentIntegrableSource.const_mul (1 / 2 : ℝ)
  have seedIdentity : Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * changed.location (source.val + 1) ^ 4) =
      changed.seed (receiver.val + 1) := by
    rw [Scales.seed, changed.adjacent_location_distance, ← adjacent]
  have adjacentBudget : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * adjacentError elapsed) ≤
      (packetBase / 2) * changed.seed (receiver.val + 1) := by
    have normalized := mul_le_mul_of_nonneg_left adjacentBoundSource (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [seedIdentity] at normalized
    simp_rw [weightedAdjacentIdentity]
    rw [intervalIntegral.integral_const_mul]
    convert normalized using 1 <;> ring
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      error elapsed ≤ coefficient * maskedState elapsed + adjacentError elapsed + remainder := by
    have triangle := norm_sum_le (Finset.univ.erase receiver) (fun index => velocity index elapsed)
    have split := General.sum_erase_eq_lower_add_adjacent_add_finer receiver source adjacent (fun index => ‖velocity index elapsed‖)
    rw [split] at triangle
    have divided := div_le_div_of_nonneg_right triangle locationPositive.le
    rw [add_div, add_div] at divided
    change ‖∑ index ∈ Finset.univ.erase receiver, velocity index elapsed‖ / changed.location (receiver.val + 1) ≤ _ at divided
    dsimp only [error]
    rw [fieldIdentity]
    exact divided.trans (add_le_add (add_le_add_right (coarse elapsed inside) _) (fine elapsed inside))
  have maskedContinuous : ContinuousOn maskedState (Icc 0 horizon) := by
    apply ContinuousOn.norm
    apply continuousOn_pi.mpr
    intro index
    by_cases selected : index.val ≤ receiver.val
    · simp only [if_pos selected]
      exact continuousOn_const.mul (((stateContinuity prepared capPositive (min_le_right _ _) path index).2.2.2).comp
        (continuousOn_const.add continuousOn_id) (fun elapsed inside => timeRange elapsed inside))
    · simp only [if_neg selected]
      exact continuousOn_const
  have exponentialContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have maskedIntegrable := (exponentialContinuous.continuousOn.mul maskedContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have exponentialIntegrable := exponentialContinuous.intervalIntegrable (μ := volume) 0 horizon
  have majorantIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (coefficient * maskedState elapsed + adjacentError elapsed + remainder)) volume 0 horizon := by
    convert ((maskedIntegrable.const_mul coefficient).add adjacentIntegrable).add
      (exponentialIntegrable.const_mul remainder) using 1
    ext elapsed
    ring
  have errorIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * error elapsed) volume 0 horizon :=
    majorantIntegrable.mono_fun' (exponentialContinuous.measurable.mul errorMeasurable).aestronglyMeasurable.restrict (by
      rw [uIoc_of_le horizonNonnegative]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (div_nonneg (norm_nonneg _) locationPositive.le))]
      exact mul_le_mul_of_nonneg_left (pointwise elapsed ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative errorIntegrable majorantIntegrable
    (fun elapsed inside => mul_le_mul_of_nonneg_left (pointwise elapsed inside) (Real.exp_pos _).le)
  have integralIdentity : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      (coefficient * maskedState elapsed + adjacentError elapsed + remainder)) =
      coefficient * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * maskedState elapsed) +
        (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * adjacentError elapsed) +
        remainder * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) coefficient, mul_comm (Real.exp _) remainder]
    rw [intervalIntegral.integral_add ((maskedIntegrable.const_mul _).add adjacentIntegrable) (exponentialIntegrable.const_mul _),
      intervalIntegral.integral_add (maskedIntegrable.const_mul _) adjacentIntegrable]
    simp only [intervalIntegral.integral_const_mul]
  have exponentialBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed)) ≤ 1 / decay := by
    simpa only [zero_mul, zero_add, one_mul, mul_one, zero_div] using
      laplace_affine_integral_bound decayPositive (by norm_num : (0 : ℝ) ≤ 0) (by norm_num : (0 : ℝ) ≤ 1) horizonNonnegative
  have remainderNonnegative : 0 ≤ remainder := mul_nonneg tolerancePositive.le
    (changed.seed_pos frequencyPositive ratioPositive _).le
  refine ⟨errorIntegrable, ?_⟩
  have actual := (comparison.trans_eq integralIdentity).trans
    (add_le_add (add_le_add_left adjacentBudget _) (mul_le_mul_of_nonneg_left exponentialBound remainderNonnegative))
  convert actual using 1 <;> dsimp only [coefficient, maskedState, remainder, error, field, decay] <;> ring

end EulerNonuniqueness.Paper

