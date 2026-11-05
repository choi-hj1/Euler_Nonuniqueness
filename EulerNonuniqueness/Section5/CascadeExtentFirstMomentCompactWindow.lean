import EulerNonuniqueness.Section5.CascadeExtentFirstMomentLocalForeignRate
import EulerNonuniqueness.Section5.CascadeRetainedCenterMomentHistory
import EulerNonuniqueness.Section5.CascadeForeignPatchAbsoluteCoefficientBound
import EulerNonuniqueness.Section5.CascadeExtentMacroSourceStateBound
import EulerNonuniqueness.General.RestartedExponentialVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem compact_moment_forcing_bound
    {extent strain centered raw difference patch epsilon kernel rawConstant patchConstant : ℝ}
    (extentOne : 1 ≤ extent) (strainNonnegative : 0 ≤ strain)
    (centeredBound : centered ≤ 2 * extent)
    (rawNonnegative : 0 ≤ raw) (rawBound : raw ≤ rawConstant)
    (differenceBound : difference ≤ 4 * kernel * strain)
    (patchNonnegative : 0 ≤ patch) (patchBound : patch ≤ patchConstant * strain)
    (epsilonSmall : epsilon ≤ 1) (kernelNonnegative : 0 ≤ kernel)
    (rawConstantNonnegative : 0 ≤ rawConstant) (patchConstantNonnegative : 0 ≤ patchConstant) :
    strain * centered + difference + epsilon * (strain * raw + patch) ≤
      (2 + 4 * kernel + rawConstant + patchConstant) * extent * strain := by
  have localBound := mul_le_mul_of_nonneg_left centeredBound strainNonnegative
  have shapeBound := add_le_add (mul_le_mul_of_nonneg_left rawBound strainNonnegative) patchBound
  have epsilonBound := mul_le_mul_of_nonneg_right epsilonSmall
    (add_nonneg (mul_nonneg strainNonnegative rawNonnegative) patchNonnegative)
  have enlarged := mul_le_mul_of_nonneg_right extentOne
    (show 0 ≤ (4 * kernel + rawConstant + patchConstant) * strain by positivity)
  nlinarith only [localBound, shapeBound, epsilonBound, differenceBound, enlarged]

theorem exists_uniform_actual_extent_firstMoment_compact_window :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ extent ≥ (1 : ℝ), ∀ span ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    let changed : Scales := {scales with frequency := frequency}
    let omega := changed.omega (index.val + 1)
    let moment := relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
    let velocity := relativeFirstMomentExternalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
    let drift := 96 / Real.pi * (2304 * changed.strain)
    ContinuousOn moment (Icc 0 path.stop) ∧ ContinuousOn velocity (Icc 0 path.stop) ∧
    (∀ time ∈ Icc 0 path.stop, HasDerivAt moment (velocity time) time) ∧ drift * span / omega ≤ 1 ∧
    ∀ start ∈ Icc 0 path.stop, ∀ finish ∈ Icc start path.stop,
      IntervalIntegrable velocity volume start finish ∧
      IntervalIntegrable (fun time => ‖velocity time‖) volume start finish ∧
      IntervalIntegrable (fun time => ‖moment time‖) volume start finish ∧
      moment finish = moment start + ∫ time in start..finish, velocity time ∧
      (omega * (finish - start) ≤ span →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
            quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤ extent * changed.length (index.val + 1)) →
        (∀ time ∈ Icc start finish, ∀ patch,
          ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
            extent * changed.length (index.val + 1)) →
        (∀ time ∈ Icc start finish,
          ‖velocity time‖ ≤ drift * ‖moment time‖ + constant * extent ^ 3 * changed.strain) ∧
        ‖moment finish‖ ≤ Real.exp 1 *
          (‖moment start‖ + constant * extent ^ 3 * changed.strain * span / omega)) := by
  obtain ⟨rateCap, ratePositive, rateFactory⟩ := exists_uniform_actual_extent_firstMoment_local_foreign_rate
  obtain ⟨shapeCap, shapePositive, rawConstant, rawNonnegative, rawIdentity, rawFactory⟩ :=
    exists_uniform_actual_extent_macro_source_state_bound
  let rawCap := min rateCap shapeCap
  have capPositive : 0 < rawCap := lt_min ratePositive shapePositive
  have rateCapBound : rawCap ≤ rateCap := min_le_left _ _
  have shapeCapBound : rawCap ≤ shapeCap := min_le_right _ _
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨rateConstant, rateNonnegative, rateParameters⟩ := rateFactory factorPositive factorSmall
  obtain ⟨patchConstant, patchNonnegative, patchFactory⟩ :=
    exists_uniform_actual_foreign_patch_absolute_coefficient_bound factor factorPositive factorOne
  let kernel := 96 / Real.pi * 2304
  let constant := rateConstant * (2 + 4 * kernel + rawConstant + patchConstant)
  have kernelNonnegative : 0 ≤ kernel := by dsimp only [kernel]; positivity
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  refine ⟨constant, constantNonnegative, ?_⟩
  intro extent extentOne span spanNonnegative scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    threshold referenceConstant scaleRoot boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [rateParameters extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound]) (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (max 1 (kernel * span))]
    with frequency rateEstimate patchEstimate blockEstimate radiusSmall strainSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let omega := changed.omega (index.val + 1)
  let moment := relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let velocity := relativeFirstMomentExternalVelocity changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let drift := 96 / Real.pi * (2304 * changed.strain)
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have frequencyOmega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) (index.val + 1)
  have omegaPositive : 0 < omega := (zero_lt_one.trans_le frequencyOne).trans_le frequencyOmega
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have driftNonnegative : 0 ≤ drift := by dsimp only [drift]; positivity
  have driftBound : drift ≤ kernel := by
    simpa only [drift, kernel, mul_assoc, mul_one] using mul_le_mul_of_nonneg_left strainSmall.le kernelNonnegative
  have driftMargin : drift * span / omega ≤ 1 := by
    apply (div_le_one omegaPositive).mpr
    exact (mul_le_mul_of_nonneg_right driftBound spanNonnegative).trans
      (((le_max_right _ _).trans frequencyLarge).trans frequencyOmega)
  have epsilonSmall : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    have actual := (radiusSmall (index.val + 1)).le
    simp only [one_mul] at actual
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le actual 2
  have derivative (time : ℝ) (inside : time ∈ Icc 0 path.stop) : HasDerivAt moment (velocity time) time :=
    path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index inside
  have momentContinuous : ContinuousOn moment (Icc 0 path.stop) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have velocityContinuous : ContinuousOn velocity (Icc 0 path.stop) :=
    path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index
  have centerInvariant : (prepared.enlargeCap rateCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawInvariant : (prepared.enlargeCap rateCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have shapeCenterInvariant : (prepared.enlargeCap shapeCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have shapeRawInvariant : (prepared.enlargeCap shapeCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  refine ⟨momentContinuous, velocityContinuous, derivative, driftMargin, ?_⟩
  intro start startInside finish finishInside
  have subset : Icc start finish ⊆ Icc 0 path.stop :=
    fun time inside => ⟨startInside.1.trans inside.1, inside.2.trans finishInside.2⟩
  have retained := path.relative_firstMoment_retained_history amplitudePositive frequencyPositive ratioPositive index
    startInside.1 finishInside.1 finishInside.2
  refine ⟨retained.1, retained.2.1,
    (momentContinuous.norm.mono subset).intervalIntegrable_of_Icc finishInside.1, retained.2.2.1, ?_⟩
  intro spanBound firstExtent secondExtent
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) :
      ‖velocity time‖ ≤ drift * ‖moment time‖ + constant * extent ^ 3 * changed.strain := by
    have globalInside := subset inside
    have actualRaw := rawFactory extent (by linarith only [extentOne]) (prepared.enlargeCap shapeCapBound) path time globalInside index
    rw [shapeRawInvariant, shapeCenterInvariant] at actualRaw
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualRaw
    have rawBound := actualRaw.1
    have referenceExtent := secondExtent time inside
    rw [prepared.referenceIdentity] at referenceExtent
    have centeredBound := (actualRaw.2 referenceExtent (firstExtent time inside)).1
    have blockData (side : Fin 2) := blockEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time globalInside index side
    have firstBlock := blockData 0
    have secondBlock := blockData 1
    have referenceMotion : cascadePairedMotion prepared.toCascadeMaterialPreparedPair 1 =
        prepared.referenceWitness.trajectory.movingFamily.patchMotion := by
      change prepared.reference = _
      exact prepared.referenceIdentity
    simp only [referenceMotion] at secondBlock
    let firstCoefficient := quadrupoleExteriorCoefficient changed prepared.trajectory.movingFamily.patchMotion index time radius
    let secondCoefficient := quadrupoleExteriorCoefficient changed prepared.referenceWitness.trajectory.movingFamily.patchMotion index time radius
    change Summable (fun power => ‖firstCoefficient power‖) ∧ ‖firstCoefficient 0‖ ≤ drift ∧
      (∑' power : ℕ, ‖firstCoefficient (power + 1)‖) ≤ drift at firstBlock
    change Summable (fun power => ‖secondCoefficient power‖) ∧ ‖secondCoefficient 0‖ ≤ drift ∧
      (∑' power : ℕ, ‖secondCoefficient (power + 1)‖) ≤ drift at secondBlock
    have firstSum : (∑' power : ℕ, ‖firstCoefficient power‖) ≤ 2 * drift := by
      rw [firstBlock.1.tsum_eq_zero_add]
      exact (add_le_add firstBlock.2.1 firstBlock.2.2).trans_eq (by ring)
    have secondSum : (∑' power : ℕ, ‖secondCoefficient power‖) ≤ 2 * drift := by
      rw [secondBlock.1.tsum_eq_zero_add]
      exact (add_le_add secondBlock.2.1 secondBlock.2.2).trans_eq (by ring)
    have pairedSummable := Summable.of_nonneg_of_le (fun power => norm_nonneg (firstCoefficient power - secondCoefficient power))
      (fun power => norm_sub_le (firstCoefficient power) (secondCoefficient power)) (firstBlock.1.add secondBlock.1)
    have blockBound : (∑' power : ℕ, ‖firstCoefficient power - secondCoefficient power‖) ≤ 4 * kernel * changed.strain := by
      have comparison := pairedSummable.tsum_le_tsum (fun power => norm_sub_le (firstCoefficient power) (secondCoefficient power))
        (firstBlock.1.add secondBlock.1)
      rw [firstBlock.1.tsum_add secondBlock.1] at comparison
      dsimp only [drift, kernel] at firstSum secondSum ⊢
      nlinarith only [comparison, firstSum, secondSum]
    have patchData := patchEstimate count orbit sectionTime phase dipoleAngle prepared path index time globalInside radius
      (mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le) le_rfl
    dsimp only at patchData
    let patchSum := ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.trajectory.movingFamily.patchMotion current index patch) radius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch) radius (power + 1) time‖
    have patchSumNonnegative : 0 ≤ patchSum := Finset.sum_nonneg fun patch _ => tsum_nonneg fun power => by positivity
    have rawSumNonnegative : 0 ≤ ∑ patch, prepared.rawSourceShapeBudget time index patch := by
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have forcingBound := compact_moment_forcing_bound extentOne strainNonnegative centeredBound rawSumNonnegative rawBound
      blockBound patchSumNonnegative patchData.2 epsilonSmall kernelNonnegative rawNonnegative patchNonnegative
    have actualRate := (rateEstimate count phase dipoleAngle (prepared.enlargeCap rateCapBound) path index time globalInside
      (firstExtent time inside) (secondExtent time inside)).2
    dsimp only at actualRate
    simp only [centerInvariant, rawInvariant] at actualRate
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap] at actualRate
    have scaled := mul_le_mul_of_nonneg_left forcingBound (mul_nonneg rateNonnegative (sq_nonneg extent))
    dsimp only [velocity, moment]
    rw [prepared.referenceIdentity]
    apply actualRate.trans
    apply add_le_add_left
    exact scaled.trans_eq (by dsimp only [constant]; ring)
  refine ⟨pointwise, ?_⟩
  let forcing := constant * extent ^ 3 * changed.strain
  have forcingNonnegative : 0 ≤ forcing := by dsimp only [forcing]; positivity
  have normContinuous := momentContinuous.norm.mono subset
  have forcingContinuous : ContinuousOn (fun _ : ℝ => forcing) (Icc start finish) := continuousOn_const
  have inequality (time : ℝ) (inside : time ∈ Icc start finish) :
      ‖moment time‖ ≤ ‖moment start‖ * Real.exp (0 * (time - start)) +
        1 * ∫ current in start..time, Real.exp (0 * (time - current)) * (forcing + drift * ‖moment current‖) := by
    have history := path.relative_firstMoment_retained_history amplitudePositive frequencyPositive ratioPositive index
      startInside.1 inside.1 (inside.2.trans finishInside.2)
    have velocityI := history.2.1
    have majorantContinuous : ContinuousOn (fun current => forcing + drift * ‖moment current‖) (Icc start time) :=
      forcingContinuous.mono (Icc_subset_Icc le_rfl inside.2) |>.add
        (continuousOn_const.mul (normContinuous.mono (Icc_subset_Icc le_rfl inside.2)))
    have comparison := intervalIntegral.integral_mono_on inside.1 velocityI
      (majorantContinuous.intervalIntegrable_of_Icc inside.1) (fun current member => by
        simpa only [add_comm] using pointwise current ⟨member.1, member.2.trans inside.2⟩)
    simpa only [zero_mul, Real.exp_zero, mul_one, one_mul] using
      history.2.2.2.trans (add_le_add_left comparison ‖moment start‖)
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall_on_Icc normContinuous forcingContinuous
    driftNonnegative (by norm_num : (0 : ℝ) ≤ 1) finishInside.1 inequality finish ⟨finishInside.1, le_rfl⟩
  have durationBound : finish - start ≤ span / omega := (le_div_iff₀ omegaPositive).mpr (by simpa only [mul_comm] using spanBound)
  have exponentBound : drift * (finish - start) ≤ 1 :=
    (mul_le_mul_of_nonneg_left durationBound driftNonnegative).trans (by simpa only [div_eq_mul_inv, mul_assoc] using driftMargin)
  have kernelBound (current : ℝ) (inside : current ∈ Icc start finish) : Real.exp (drift * (finish - current)) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((mul_le_mul_of_nonneg_left (sub_le_sub_left inside.1 finish) driftNonnegative).trans exponentBound)
  have exponentialContinuous : ContinuousOn (fun current => Real.exp (drift * (finish - current)) * forcing) (Icc start finish) := by fun_prop
  have integralBound := intervalIntegral.integral_mono_on finishInside.1
    (exponentialContinuous.intervalIntegrable_of_Icc finishInside.1)
    (continuousOn_const.intervalIntegrable_of_Icc (μ := volume) finishInside.1)
    (fun current member => mul_le_mul_of_nonneg_right (kernelBound current member) forcingNonnegative)
  simp only [intervalIntegral.integral_const, smul_eq_mul] at integralBound
  have finalBound := resolved.2.2
  simp only [one_mul, zero_add] at finalBound
  have initialBound := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr exponentBound) (norm_nonneg (moment start))
  calc
    ‖moment finish‖ ≤ ‖moment start‖ * Real.exp 1 + (finish - start) * (Real.exp 1 * forcing) :=
      finalBound.trans (add_le_add initialBound integralBound)
    _ = Real.exp 1 * (‖moment start‖ + forcing * (finish - start)) := by ring
    _ ≤ Real.exp 1 * (‖moment start‖ + forcing * (span / omega)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left durationBound forcingNonnegative) _) (Real.exp_pos 1).le
    _ = Real.exp 1 * (‖moment start‖ + forcing * span / omega) := by ring
    _ = _ := rfl

end EulerNonuniqueness.Paper
