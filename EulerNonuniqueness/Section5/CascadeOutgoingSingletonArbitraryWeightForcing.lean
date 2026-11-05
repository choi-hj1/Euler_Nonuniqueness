import EulerNonuniqueness.Section6.SourcePacketPairedBlockCenterArbitraryWeightBudget
import EulerNonuniqueness.Section6.SourcePacketPairedPatchCoefficientArbitraryWeightBudget
import EulerNonuniqueness.Section6.SourcePacketPairedPatchVelocityArbitraryWeightBudget
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity
import EulerNonuniqueness.Section6.SourcePacketPairedLeadingArbitraryWeightBudget

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem outgoing_six_piece_integral_bound
    {leading block : ℝ → ℝ} {macroPatch own physical velocity : Fin 4 → ℝ → ℝ}
    {horizon epsilon leadingConstant blockConstant patchConstant velocityConstant cost : ℝ}
    (epsilonNonnegative : 0 ≤ epsilon) (epsilonOne : epsilon ≤ 1)
    (patchNonnegative : 0 ≤ patchConstant) (costNonnegative : 0 ≤ cost)
    (leadingI : IntervalIntegrable leading volume 0 horizon)
    (blockI : IntervalIntegrable block volume 0 horizon)
    (macroI : ∀ patch, IntervalIntegrable (macroPatch patch) volume 0 horizon)
    (ownI : ∀ patch, IntervalIntegrable (own patch) volume 0 horizon)
    (physicalI : ∀ patch, IntervalIntegrable (physical patch) volume 0 horizon)
    (velocityI : ∀ patch, IntervalIntegrable (velocity patch) volume 0 horizon)
    (leadingBound : (∫ time in (0 : ℝ)..horizon, leading time) ≤ leadingConstant * cost)
    (blockBound : (∫ time in (0 : ℝ)..horizon, block time) ≤ blockConstant * cost)
    (macroBound : ∀ patch, (∫ time in (0 : ℝ)..horizon, macroPatch patch time) ≤ patchConstant * cost)
    (ownBound : ∀ patch, (∫ time in (0 : ℝ)..horizon, own patch time) ≤ patchConstant * cost)
    (physicalBound : ∀ patch, (∫ time in (0 : ℝ)..horizon, physical patch time) ≤ patchConstant * cost)
    (velocityBound : ∀ patch, (∫ time in (0 : ℝ)..horizon, velocity patch time) ≤ velocityConstant * cost) :
    (∫ time in (0 : ℝ)..horizon,
      leading time + block time + epsilon * (∑ patch, macroPatch patch time) + epsilon * (∑ patch, own patch time) +
        (∑ patch, physical patch time) + (∑ patch, velocity patch time) / 4) ≤
      (leadingConstant + blockConstant + 12 * patchConstant + velocityConstant) * cost := by
  have macroSumI : IntervalIntegrable (fun time => ∑ patch, macroPatch patch time) volume 0 horizon := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum (s := Finset.univ) (f := macroPatch) (fun patch _ => macroI patch)
  have ownSumI : IntervalIntegrable (fun time => ∑ patch, own patch time) volume 0 horizon := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum (s := Finset.univ) (f := own) (fun patch _ => ownI patch)
  have physicalSumI : IntervalIntegrable (fun time => ∑ patch, physical patch time) volume 0 horizon := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum (s := Finset.univ) (f := physical) (fun patch _ => physicalI patch)
  have velocitySumI : IntervalIntegrable (fun time => ∑ patch, velocity patch time) volume 0 horizon := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum (s := Finset.univ) (f := velocity) (fun patch _ => velocityI patch)
  have finiteBound (values : Fin 4 → ℝ) {bound : ℝ} (bounds : ∀ patch, values patch ≤ bound) :
      (∑ patch, values patch) ≤ 4 * bound := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => bounds patch)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] using summed
  have macroTotal := finiteBound _ macroBound
  have ownTotal := finiteBound _ ownBound
  have physicalTotal := finiteBound _ physicalBound
  have velocityTotal := finiteBound _ velocityBound
  have patchCostNonnegative : 0 ≤ 4 * (patchConstant * cost) := by positivity
  have macroScaled := (mul_le_mul_of_nonneg_left macroTotal epsilonNonnegative).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right epsilonOne patchCostNonnegative)
  have ownScaled := (mul_le_mul_of_nonneg_left ownTotal epsilonNonnegative).trans
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right epsilonOne patchCostNonnegative)
  rw [intervalIntegral.integral_add ((((leadingI.add blockI).add (macroSumI.const_mul epsilon)).add
      (ownSumI.const_mul epsilon)).add physicalSumI) (velocitySumI.div_const 4),
    intervalIntegral.integral_add (((leadingI.add blockI).add (macroSumI.const_mul epsilon)).add
      (ownSumI.const_mul epsilon)) physicalSumI,
    intervalIntegral.integral_add ((leadingI.add blockI).add (macroSumI.const_mul epsilon)) (ownSumI.const_mul epsilon),
    intervalIntegral.integral_add (leadingI.add blockI) (macroSumI.const_mul epsilon),
    intervalIntegral.integral_add leadingI blockI, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
    intervalIntegral.integral_finset_sum (fun patch _ => macroI patch),
    intervalIntegral.integral_finset_sum (fun patch _ => ownI patch),
    intervalIntegral.integral_finset_sum (fun patch _ => physicalI patch),
    intervalIntegral.integral_finset_sum (fun patch _ => velocityI patch)]
  linear_combination leadingBound + blockBound + macroScaled + ownScaled + physicalTotal + velocityTotal / 4

private theorem outgoing_singleton_window_translation (input : ℝ → ℝ) (weight start horizon : ℝ) :
    (∫ time in start..start + horizon, Real.exp (-weight * time) * input time) =
      Real.exp (-weight * start) *
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * input (start + elapsed) := by
  have shift := intervalIntegral.integral_comp_add_left
    (f := fun time => Real.exp (-weight * time) * input time) (a := 0) (b := horizon) start
  rw [add_zero] at shift
  rw [← shift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [show -weight * (start + elapsed) = -weight * start + -weight * elapsed by ring, Real.exp_add]
  ring

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_actual_outgoing_singleton_arbitrary_weight_forcing :
    ∃ thresholdRadius > (0 : ℝ), thresholdRadius ≤ 1 / 8 ∧ ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdRadius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {cap shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair cap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ receiver drive source : Fin count,
    receiver.val ≤ drive.val → drive.val < source.val →
    ∀ start horizon initialDistance : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    512 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    ‖firstDipoleSeparation first start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation first start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter first start source - secondDipoleCenter first start source)).re →
    ‖firstDipoleCenter first start source - secondDipoleCenter first start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
    let forcing := prepared.selectedForeignForcing {source} receiver
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 4) +
      (1 + initialDistance) * changed.circulation (source.val + 1) * length ^ 2 / (weight * distance ^ 4) +
      changed.circulation (source.val + 1) * ‖centroidAsymmetry first start source‖ / (weight * distance ^ 3)
    (∀ time ∈ Icc 0 path.stop,
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) ∧
      ∀ patch : Fin 4, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source)) ∧
    ContinuousOn forcing (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * forcing (start + elapsed)) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * forcing (start + elapsed)) ≤ constant * cost ∧
    (∫ time in (0 : ℝ)..start + horizon, Real.exp (-weight * time) * forcing time) ≤
      (∫ time in (0 : ℝ)..start, Real.exp (-weight * time) * forcing time) + Real.exp (-weight * start) * (constant * cost) := by
  obtain ⟨leadingThreshold, leadingPositive, leadingEighth, leadingConstant, leadingNonnegative, leadingFactory⟩ :=
    exists_actual_paired_leading_arbitrary_weight_budget
  obtain ⟨blockThreshold, blockPositive, _, blockConstant, blockNonnegative, blockFactory⟩ :=
    exists_actual_paired_blockcenter_source_arbitrary_weight_budget
  obtain ⟨patchThreshold, patchPositive, _, patchConstant, patchNonnegative, patchFactory⟩ :=
    exists_actual_paired_patch_coefficient_arbitrary_weight_budget
  obtain ⟨velocityThreshold, velocityPositive, _, velocityConstant, velocityNonnegative, velocityFactory⟩ :=
    exists_actual_paired_patch_velocity_arbitrary_weight_budget
  let thresholdRadius := min leadingThreshold (min blockThreshold (min patchThreshold velocityThreshold))
  let constant := leadingConstant + blockConstant + 12 * patchConstant + velocityConstant
  refine ⟨thresholdRadius, lt_min leadingPositive (lt_min blockPositive (lt_min patchPositive velocityPositive)),
    (min_le_left _ _).trans leadingEighth, constant, by dsimp only [constant]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
    threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall rootOne boundaryOne
  have leadingBound := thresholdBound.trans (min_le_left _ _)
  have blockBound := thresholdBound.trans ((min_le_right _ _).trans (min_le_left _ _))
  have patchBound := thresholdBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have velocityBound := thresholdBound.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have thresholdSmall : threshold ≤ 1 / 8 := leadingBound.trans leadingEighth
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have ratioOne : 1 ≤ scales.ratio := by linarith only [ratioBound]
  filter_upwards [leadingFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold leadingBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    blockFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold blockBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold patchBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    velocityFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative referenceAmplitude
      threshold velocityBound orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorEighth rootOne boundaryOne,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_individual_source_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_radius_lt_length amplitudePositive ratioOne (by positivity : 0 < factor / 39321600),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_ge_atTop (1 : ℝ)]
    with frequency leadingEstimate blockEstimate patchEstimate velocityEstimate selectedContinuity seriesContinuity radii lengths frequencyOne
  intro count phase dipoleAngle cap shapeRadius monitor prepared path receiver drive source receiverBefore driveBefore
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper weight weightBound
  let changed : Scales := {scales with frequency := frequency}
  let location := changed.location (receiver.val + 1)
  let distance := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let macroRadius := factor / 39321600 * location
  let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
  let epsilon := changed.radius (receiver.val + 1) ^ 2 / changed.length (receiver.val + 1) ^ 2
  let forcing := prepared.selectedForeignForcing {source} receiver
  let cost := changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 4) +
    (1 + initialDistance) * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / (weight * distance ^ 4) +
    changed.circulation (source.val + 1) * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion start source‖ / (weight * distance ^ 3)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have weightPositive : 0 < weight := (changed.omega_pos frequencyPositive ratioPositive _).trans_le weightBound
  have locationPositive : 0 < location := changed.location_pos _
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have finer : receiver.val + 1 < source.val + 1 := by omega
  have sourceHalf := changed.location_le_half_of_lt finer
  have distanceIdentity : distance = location - changed.location (source.val + 1) := abs_of_nonneg (by linarith only [sourceHalf, locationPositive])
  have distancePositive : 0 < distance := changed.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have distanceLower : location / 2 ≤ distance := by rw [distanceIdentity]; linarith only [sourceHalf]
  have distanceUpper : distance ≤ location := by rw [distanceIdentity]; linarith only [changed.location_pos (source.val + 1)]
  have lengthBelow : changed.length (receiver.val + 1) ≤ location := by simpa only [one_mul] using (lengths (receiver.val + 1)).le
  have scalarNonnegative : 0 ≤ factor / 39321600 := by positivity
  have macroNonnegative : 0 ≤ macroRadius := mul_nonneg scalarNonnegative locationPositive.le
  have macroSmall : macroRadius ≤ distance / (100000 * 96) := by
    dsimp only [macroRadius]
    nlinarith only [mul_le_mul_of_nonneg_right factorSmall locationPositive.le, distanceLower, locationPositive]
  have macroReceiverSmall : macroRadius ≤ location / (100000 * 96) :=
    macroSmall.trans (div_le_div_of_nonneg_right distanceUpper (by norm_num))
  have ownNonnegative : 0 ≤ ownRadius := mul_nonneg scalarNonnegative (changed.length_pos _).le
  have ownMacro : ownRadius ≤ macroRadius := mul_le_mul_of_nonneg_left lengthBelow scalarNonnegative
  have physicalNonnegative : 0 ≤ changed.radius (receiver.val + 1) := Real.sqrt_nonneg _
  have physicalLength : changed.radius (receiver.val + 1) ≤ factor / 39321600 * changed.length (receiver.val + 1) := (radii (receiver.val + 1)).le
  have physicalMacro := physicalLength.trans ownMacro
  have epsilonNonnegative : 0 ≤ epsilon := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have epsilonOne : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos (changed.length_pos _))).mpr
    have lengthBound : changed.radius (receiver.val + 1) ≤ changed.length (receiver.val + 1) :=
      physicalLength.trans (by nlinarith only [factorSmall, changed.length_pos (receiver.val + 1)])
    exact pow_le_pow_left₀ physicalNonnegative lengthBound 2
  have circulationPositive := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
  have initialNonnegative : 0 ≤ initialDistance := by linarith only [initialLarge]
  have costNonnegative : 0 ≤ cost := by dsimp only [cost]; positivity
  have leadingData := leadingEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive source receiverBefore driveBefore
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper weight weightBound
  have blockData := blockEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive source receiverBefore driveBefore
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper macroRadius macroNonnegative macroSmall weight weightBound
  have patchData (patch : Fin 4) (radius : ℝ) (nonnegative : 0 ≤ radius) (small : radius ≤ distance / (100000 * 96)) :=
    patchEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive source receiverBefore driveBefore patch
      start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
      firstInitial secondInitial initialProjection initialUpper radius nonnegative small weight weightBound
  have velocityData (patch : Fin 4) := velocityEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive source receiverBefore driveBefore patch
    start horizon initialDistance startNonnegative horizonNonnegative endBound initialLarge initialSmall direction directionNorm
    firstInitial secondInitial initialProjection initialUpper weight weightBound
  have block96 (time : ℝ) (inside : time ∈ Icc 0 path.stop) : Summable (fun power : ℕ =>
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) := blockData.2.1 time inside
  have blockDominated (time : ℝ) (power : ℕ) : prepared.coarserBlockCoefficientTerm receiver macroRadius time source power ≤
      (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power :=
    le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num))
  have blockUnweighted (time : ℝ) (inside : time ∈ Icc 0 path.stop) : Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (blockDominated time) (block96 time inside)
  have summable (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) ∧
      Summable (prepared.coarserBlockCoefficientTerm receiver macroRadius time source) ∧
      ∀ patch : Fin 4, Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) macroRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) ownRadius time source) ∧
        Summable (prepared.coarserPatchCoefficientTerm (receiver, patch) (changed.radius (receiver.val + 1)) time source) :=
    ⟨block96 time inside, blockUnweighted time inside, fun patch =>
      ⟨(patchData patch macroRadius macroNonnegative macroSmall).2.1 time inside,
        (patchData patch ownRadius ownNonnegative (ownMacro.trans macroSmall)).2.1 time inside,
        (patchData patch _ physicalNonnegative (physicalMacro.trans macroSmall)).2.1 time inside⟩⟩
  have selectedSubset : ({source} : Finset (Fin count)) ⊆ Finset.univ.erase receiver := by
    simpa only [Finset.singleton_subset_iff, Finset.mem_erase, Finset.mem_univ, and_true] using different.symm
  have forcingContinuous : ContinuousOn forcing (Icc 0 path.stop) :=
    (selectedContinuity count phase dipoleAngle prepared path receiver {source} selectedSubset).2.1
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith only [startNonnegative, inside.1], by linarith only [endBound, inside.2]⟩
  have windowI (function : ℝ → ℝ) (regular : ContinuousOn function (Icc 0 path.stop)) :
      IntervalIntegrable (fun elapsed => Real.exp (-weight * elapsed) * function (start + elapsed)) volume 0 horizon :=
    ((by fun_prop : Continuous (fun elapsed : ℝ => Real.exp (-weight * elapsed)))).continuousOn.mul
      (regular.comp (continuous_const.add continuous_id).continuousOn timeRange) |>.intervalIntegrable_of_Icc horizonNonnegative
  have blockContinuous : ContinuousOn (fun time => ∑' power : ℕ, prepared.coarserBlockCoefficientTerm receiver macroRadius time source power) (Icc 0 path.stop) :=
    (seriesContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source different macroRadius macroNonnegative macroReceiverSmall).2.1
  have blockWindowI := windowI _ blockContinuous
  have blockComparison := intervalIntegral.integral_mono_on horizonNonnegative blockWindowI blockData.2.2.2.2.1
    (fun elapsed inside => mul_le_mul_of_nonneg_left ((blockUnweighted _ (timeRange elapsed inside)).tsum_le_tsum
      (blockDominated _) (block96 _ (timeRange elapsed inside))) (Real.exp_pos _).le)
  have blockBudget := blockComparison.trans blockData.2.2.2.2.2.1
  let velocity := fun (patch : Fin 4) time => ‖biotSavart (quadrupoleDensity changed prepared.trajectory.movingFamily.patchMotion time source)
    (patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver patch) -
      biotSavart (quadrupoleDensity changed prepared.referenceWitness.trajectory.movingFamily.patchMotion time source)
        (patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver patch)‖
  have velocityBudget (patch : Fin 4) : (∫ elapsed in (0 : ℝ)..horizon,
      (Real.exp (-weight * elapsed) * velocity patch (start + elapsed)) / location) ≤ velocityConstant * cost := by
    rw [intervalIntegral.integral_div]
    have divided := div_le_div_of_nonneg_right (velocityData patch).2.2.2.1 locationPositive.le
    have costIdentity : changed.circulation (source.val + 1) ^ 2 / (weight ^ 2 * distance ^ 3) +
        (1 + initialDistance) * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 / (weight * distance ^ 3) +
        changed.circulation (source.val + 1) * ‖centroidAsymmetry prepared.trajectory.movingFamily.patchMotion start source‖ / (weight * distance ^ 2) = distance * cost := by
      dsimp only [cost]; field_simp; ring
    rw [costIdentity] at divided
    exact divided.trans (by
      have scaled := mul_le_mul_of_nonneg_left distanceUpper (mul_nonneg velocityNonnegative costNonnegative)
      apply (div_le_iff₀ locationPositive).mpr
      nlinarith only [scaled])
  have combined := outgoing_six_piece_integral_bound epsilonNonnegative epsilonOne patchNonnegative costNonnegative
    leadingData.2.2.1 blockWindowI
    (fun patch => (patchData patch macroRadius macroNonnegative macroSmall).2.2.2.2.1)
    (fun patch => (patchData patch ownRadius ownNonnegative (ownMacro.trans macroSmall)).2.2.2.2.1)
    (fun patch => (patchData patch _ physicalNonnegative (physicalMacro.trans macroSmall)).2.2.2.2.1)
    (fun patch => (velocityData patch).2.2.1.div_const location)
    leadingData.2.2.2.1 blockBudget
    (fun patch => (patchData patch macroRadius macroNonnegative macroSmall).2.2.2.2.2.1)
    (fun patch => (patchData patch ownRadius ownNonnegative (ownMacro.trans macroSmall)).2.2.2.2.2.1)
    (fun patch => (patchData patch _ physicalNonnegative (physicalMacro.trans macroSmall)).2.2.2.2.2.1) velocityBudget
  have windowBound : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-weight * elapsed) * forcing (start + elapsed)) ≤ constant * cost := by
    convert combined using 1
    apply intervalIntegral.integral_congr
    intro elapsed _
    dsimp only [forcing, CascadeSourcePreparedPair.selectedForeignForcing,
      CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm, velocity]
    simp only [Finset.sum_singleton, prepared.referenceIdentity, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  have originalContinuous := (by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * time))).continuousOn.mul forcingContinuous
  have startBound : start ≤ path.stop := by linarith only [endBound, horizonNonnegative]
  have prefixI := (originalContinuous.mono (Icc_subset_Icc le_rfl startBound)).intervalIntegrable_of_Icc (μ := volume) startNonnegative
  have physicalWindowI := (originalContinuous.mono (Icc_subset_Icc startNonnegative endBound)).intervalIntegrable_of_Icc
    (μ := volume) (show start ≤ start + horizon by linarith only [horizonNonnegative])
  refine ⟨summable, forcingContinuous,
    (originalContinuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc (μ := volume) (add_nonneg startNonnegative horizonNonnegative),
    windowI forcing forcingContinuous, windowBound, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals prefixI physicalWindowI,
    outgoing_singleton_window_translation forcing weight start horizon]
  exact add_le_add_left (mul_le_mul_of_nonneg_left windowBound (Real.exp_pos _).le) _

end EulerNonuniqueness.Paper
