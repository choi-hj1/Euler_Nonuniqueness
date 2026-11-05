import EulerNonuniqueness.Section5.CascadeFollowerResolvedResponse
import EulerNonuniqueness.Section5.CascadeFollowerForcingRow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_follower_return_kernel :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (2 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    let changed : Scales := {scales with frequency := frequency}
    let envelope := prepared.coarserFollowerEnvelope drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let driver := fun time => prepared.weightedMacroSourceState time drive
    let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
    let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    ContinuousOn returned (Icc 0 finish) ∧
    IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable driver volume 0 finish ∧
    IntervalIntegrable remaining volume 0 finish ∧ IntervalIntegrable returned volume 0 finish ∧
    envelope 0 = 0 ∧ rate ≤ changed.omega (drive.val + 1) ∧
    changed.omega (drive.val + 1) < 2 * Real.sqrt 2 * changed.omega (drive.val + 1) ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * driver current) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * remaining current) volume 0 time ∧
      returned time ≤ constant * rho * driver time +
        constant * rho * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * remaining current) +
        constant * rho ^ 2 * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, responseCap, responsePositive, responseFactory⟩ :=
    exists_uniform_actual_follower_resolved_response
  obtain ⟨rowCap, rowPositive, rowConstant, rowNonnegative, rows⟩ := exists_uniform_actual_follower_forcing_row
  let rawCap := min responseCap rowCap
  have rawPositive : 0 < rawCap := lt_min responsePositive rowPositive
  have responseCapBound : rawCap ≤ responseCap := min_le_left _ _
  have rowCapBound : rawCap ≤ rowCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseConstant, responseOne, rootMin, rootEight, responses⟩ :=
    responseFactory factorPositive factorSmall
  let constant := responseConstant * (1 + rowConstant)
  have responseNonnegative : 0 ≤ responseConstant := zero_le_one.trans responseOne
  have responseBelow : responseConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [mul_nonneg responseNonnegative rowNonnegative]
  have constantOne : 1 ≤ constant := responseOne.trans responseBelow
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have productBelow : responseConstant * rowConstant ≤ constant := by
    dsimp only [constant]
    nlinarith only [responseNonnegative]
  have rowBelowProduct : rowConstant ≤ responseConstant * rowConstant := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right responseOne rowNonnegative
  have rowBelow : rowConstant ≤ constant := rowBelowProduct.trans productBelow
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have responseRatio : max 2 (2 * responseConstant) ≤ scales.ratio :=
    max_le ratioBound ((mul_le_mul_of_nonneg_left responseBelow (by norm_num : (0 : ℝ) ≤ 2)).trans
      ((le_max_right _ _).trans ratioLarge))
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := by linarith only [factorSmall]
  have feedbackDecay : Tendsto (fun frequency : ℝ => constant *
      (216360000 * ({scales with frequency := frequency}).hessian +
        576 * ({scales with frequency := frequency}).strain)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)).const_mul constant
  filter_upwards [responses scales scaleRoot rootLarge amplitudeIdentity responseRatio alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    rows scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne
      boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    feedbackDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℝ)] with frequency response row selectedContinuous feedbackSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive driveNonterminal finish finishNonnegative finishBound small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let envelope := prepared.coarserFollowerEnvelope drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
  let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let oldRate := responseConstant * changed.omega (drive.val + 1) / changed.ratio + responseConstant * rho
  let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
  have macroCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have weightedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext current source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroCapInvariant]
  have envelopeCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).coarserFollowerEnvelope = prepared.coarserFollowerEnvelope := by
    funext currentDrive current
    simp only [CascadeSourcePreparedPair.coarserFollowerEnvelope, weightedCapInvariant]
  have remainingCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).followerStrictlyFinerForcing = prepared.followerStrictlyFinerForcing := rfl
  have selectedCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).selectedForeignForcing = prepared.selectedForeignForcing := rfl
  have actual := response count phase dipoleAngle (prepared.enlargeCap responseCapBound) path drive driveNonterminal
    finish finishNonnegative finishBound small
  dsimp only at actual
  simp only [envelopeCapInvariant, weightedCapInvariant, remainingCapInvariant] at actual
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, envelopeIntegrable, driverIntegrable,
    remainingIntegrable, initialZero, oldRateBound, unstableGap, resolved⟩ := actual
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioOne : 1 ≤ changed.ratio := by change 1 ≤ scales.ratio; linarith only [ratioBound]
  have ratioPositive : 0 < changed.ratio := zero_lt_one.trans_le ratioOne
  have omegaOne : 1 ≤ changed.omega (drive.val + 1) :=
    frequencyOne.trans (changed.omega_ge_frequency frequencyPositive ratioOne _)
  have omegaPositive : 0 < changed.omega (drive.val + 1) := zero_lt_one.trans_le omegaOne
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho]
    positivity
  have driverNonnegative (time : ℝ) : 0 ≤ driver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time drive)
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have selectedSubset : selected ⊆ Finset.univ.erase drive := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have returnedContinuous : ContinuousOn returned (Icc 0 finish) :=
    continuousOn_const.mul (((selectedContinuous count phase dipoleAngle prepared path drive selected selectedSubset).2.1).mono
      (Icc_subset_Icc le_rfl finishBound))
  have rowBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      returned time ≤ rowConstant * rho * (envelope time + driver time) := by
    have actualRow := row count phase dipoleAngle (prepared.enlargeCap rowCapBound) path time
      ⟨inside.1, inside.2.trans finishBound⟩ drive drive le_rfl
    dsimp only at actualRow
    simp only [selectedCapInvariant, envelopeCapInvariant, weightedCapInvariant, if_pos rfl] at actualRow
    exact actualRow.2.2.2
  have rateComparison : oldRate ≤ rate :=
    add_le_add (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right responseBelow omegaPositive.le) ratioPositive.le)
      (mul_le_mul_of_nonneg_right responseBelow rhoNonnegative)
  have halfRate : constant * changed.omega (drive.val + 1) / changed.ratio ≤ changed.omega (drive.val + 1) / 2 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have separated : 2 * constant ≤ changed.ratio := (le_max_right _ _).trans ratioLarge
    have comparison := mul_le_mul_of_nonneg_right separated omegaPositive.le
    nlinarith only [comparison]
  have feedbackHalf : constant * rho ≤ 1 / 2 := le_of_lt feedbackSmall
  have rateBound : rate ≤ changed.omega (drive.val + 1) := by
    calc
      rate ≤ changed.omega (drive.val + 1) / 2 + 1 / 2 := add_le_add halfRate feedbackHalf
      _ ≤ changed.omega (drive.val + 1) / 2 + changed.omega (drive.val + 1) / 2 :=
        add_le_add_left (div_le_div_of_nonneg_right omegaOne (by norm_num : (0 : ℝ) ≤ 2)) _
      _ = changed.omega (drive.val + 1) := by ring
  refine ⟨envelopeContinuous, driverContinuous, remainingContinuous, returnedContinuous, envelopeIntegrable,
    driverIntegrable, remainingIntegrable, returnedContinuous.intervalIntegrable_of_Icc finishNonnegative,
    initialZero, rateBound, unstableGap, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (rate * (time - current))) := by fun_prop
  have driverKernelIntegrable := (kernelContinuous.continuousOn.mul (driverContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have remainingKernelIntegrable := (kernelContinuous.continuousOn.mul (remainingContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  let driverAction := ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current
  let remainingAction := ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * remaining current
  have driverActionNonnegative : 0 ≤ driverAction := intervalIntegral.integral_nonneg_of_forall inside.1
    (fun current => mul_nonneg (Real.exp_pos _).le (driverNonnegative current))
  have remainingActionNonnegative : 0 ≤ remainingAction := intervalIntegral.integral_nonneg_of_forall inside.1
    (fun current => mul_nonneg (Real.exp_pos _).le (remainingNonnegative current))
  have combinedContinuous : ContinuousOn (fun current => rho * driver current + remaining current) (Icc 0 finish) :=
    (continuousOn_const.mul driverContinuous).add remainingContinuous
  have combinedIntegrable := (kernelContinuous.continuousOn.mul
    (combinedContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have enlargedIntegral : (∫ current in (0 : ℝ)..time,
      Real.exp (oldRate * (time - current)) * (rho * driver current + remaining current)) ≤
      ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * (rho * driver current + remaining current) := by
    apply intervalIntegral.integral_mono_on inside.1 (resolved time inside).1 combinedIntegrable
    intro current currentInside
    apply mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right rateComparison (sub_nonneg.mpr currentInside.2)))
      (add_nonneg (mul_nonneg rhoNonnegative (driverNonnegative current)) (remainingNonnegative current))
  have integralIdentity : (∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * (rho * driver current + remaining current)) =
      rho * driverAction + remainingAction := by
    calc
      _ = ∫ current in (0 : ℝ)..time,
          rho * (Real.exp (rate * (time - current)) * driver current) +
            Real.exp (rate * (time - current)) * remaining current := by
        apply intervalIntegral.integral_congr
        intro current _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add (driverKernelIntegrable.const_mul rho) remainingKernelIntegrable,
          intervalIntegral.integral_const_mul]
  have envelopeBound : envelope time ≤ responseConstant * (rho * driverAction + remainingAction) := by
    have estimate := (resolved time inside).2.trans (mul_le_mul_of_nonneg_left enlargedIntegral responseNonnegative)
    rw [integralIdentity] at estimate
    exact estimate
  have substituted := (rowBound time inside).trans (mul_le_mul_of_nonneg_left
    (add_le_add_right envelopeBound (driver time)) (mul_nonneg rowNonnegative rhoNonnegative))
  have directComparison := mul_le_mul_of_nonneg_right rowBelow (mul_nonneg rhoNonnegative (driverNonnegative time))
  have remainingComparison := mul_le_mul_of_nonneg_right productBelow (mul_nonneg rhoNonnegative remainingActionNonnegative)
  have driverComparison := mul_le_mul_of_nonneg_right productBelow (mul_nonneg (sq_nonneg rho) driverActionNonnegative)
  have finalComparison := add_le_add (add_le_add directComparison remainingComparison) driverComparison
  refine ⟨driverKernelIntegrable, remainingKernelIntegrable, substituted.trans ?_⟩
  convert finalComparison using 1 <;> ring

end EulerNonuniqueness.Paper
