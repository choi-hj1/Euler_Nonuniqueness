import EulerNonuniqueness.Section5.CascadeFollowerReturnKernel
import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem convolution_continuous_on_prefix {forcing : ℝ → ℝ} {finish : ℝ}
    (finishNonnegative : 0 ≤ finish) (regular : ContinuousOn forcing (Icc 0 finish)) (rate : ℝ) :
    ContinuousOn (fun time => ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current) (Icc 0 finish) := by
  let extended := fun time => forcing (projIcc 0 finish finishNonnegative time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp regular).comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 finish) :
      EulerNonuniqueness.exponentialResponse rate extended time =
        ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (rate * (time - current)) * forcing (projIcc 0 finish finishNonnegative current) = _
    rw [projIcc_of_mem finishNonnegative ⟨member.1, member.2.trans inside.2⟩]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse rate extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous rate time).continuousAt
  exact responseContinuous.continuousOn.congr (fun time inside => (agreement time inside).symm)

theorem exists_uniform_actual_follower_arbitrary_weight_return :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ constant ≥ (1 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    max 2 (4 * constant) ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ,
    threshold ≤ thresholdMax → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ (orbit : SeparatingOrbit) (sectionTime tolerance : ℝ), 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ drive : Fin count, drive.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ receiver : Fin count, receiver.val < drive.val → ∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time receiver| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time receiver| ≤ radius) →
    ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (drive.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    let envelope := prepared.coarserFollowerEnvelope drive
    let remaining := prepared.followerStrictlyFinerForcing drive
    let driver := fun time => prepared.weightedMacroSourceState time drive
    let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
    let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
    let driverResponse := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current
    let remainingResponse := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * remaining current
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    ContinuousOn returned (Icc 0 finish) ∧ ContinuousOn driverResponse (Icc 0 finish) ∧ ContinuousOn remainingResponse (Icc 0 finish) ∧
    envelope 0 = 0 ∧ rate ≤ changed.omega (drive.val + 1) / 2 ∧
    (0 < changed.omega (drive.val + 1) ∧ changed.omega (drive.val + 1) / 2 ≤ weight - rate) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * envelope time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * driver time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * remaining time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * returned time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * driverResponse time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * remainingResponse time) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * returned time) ≤
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * driver time) +
        (2 * constant * rho / changed.omega (drive.val + 1)) *
          (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * remaining time) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, factory⟩ :=
    exists_uniform_actual_follower_return_kernel
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, returns⟩ :=
    factory factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime tolerance tolerancePositive
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have parentRatio : max 2 (2 * constant) ≤ scales.ratio := by
    apply max_le ratioBound
    have bound := (le_max_right (2 : ℝ) (4 * constant)).trans ratioLarge
    linarith only [bound, constantOne]
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have rhoDecay : Tendsto (fun frequency : ℝ =>
      216360000 * ({scales with frequency := frequency}).hessian +
        576 * ({scales with frequency := frequency}).strain) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  have absorptionDecay : Tendsto (fun frequency : ℝ => constant *
      (216360000 * ({scales with frequency := frequency}).hessian + 576 * ({scales with frequency := frequency}).strain) +
      2 * constant * (216360000 * ({scales with frequency := frequency}).hessian +
        576 * ({scales with frequency := frequency}).strain) ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add] using
      (rhoDecay.const_mul constant).add ((rhoDecay.pow 2).const_mul (2 * constant))
  have feedbackDecay := rhoDecay.const_mul constant
  have quarterPositive : (0 : ℝ) < 1 / 4 := by norm_num
  filter_upwards [returns scales scaleRoot rootLarge amplitudeIdentity parentRatio alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    absorptionDecay.eventually (eventually_lt_nhds tolerancePositive),
    feedbackDecay.eventually (by simpa only [mul_zero] using eventually_lt_nhds quarterPositive),
    eventually_ge_atTop (1 : ℝ)]
    with frequency returnedBound absorptionSmall feedbackSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive driveNonterminal finish finishNonnegative finishBound small weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let envelope := prepared.coarserFollowerEnvelope drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
  let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
  let driverResponse := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current
  let remainingResponse := fun time => ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * remaining current
  have actual := returnedBound count phase dipoleAngle prepared path drive driveNonterminal finish finishNonnegative finishBound small
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, returnedContinuous, envelopeIntegrable,
    driverIntegrable, remainingIntegrable, returnedIntegrable, initialZero, rateBound, unstableGap, pointwise⟩ := actual
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
  have geometricQuarter : constant * changed.omega (drive.val + 1) / changed.ratio ≤
      changed.omega (drive.val + 1) / 4 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have separated : 4 * constant ≤ changed.ratio := (le_max_right _ _).trans ratioLarge
    have comparison := mul_le_mul_of_nonneg_right separated omegaPositive.le
    nlinarith only [comparison]
  have slowRateBound : rate ≤ changed.omega (drive.val + 1) / 2 := by
    have feedbackQuarter : constant * rho ≤ 1 / 4 := le_of_lt feedbackSmall
    dsimp only [rate]
    linarith only [geometricQuarter, feedbackQuarter, omegaOne]
  have gapBound : changed.omega (drive.val + 1) / 2 ≤ weight - rate := by
    linarith only [slowRateBound, weightBound]
  have gapPositive : 0 < weight - rate := (half_pos omegaPositive).trans_le gapBound
  have inverseBound (numerator : ℝ) (nonnegative : 0 ≤ numerator) :
      numerator / (weight - rate) ≤ 2 * numerator / changed.omega (drive.val + 1) := by
    calc
      _ ≤ numerator / (changed.omega (drive.val + 1) / 2) :=
        div_le_div_of_nonneg_left nonnegative (half_pos omegaPositive) gapBound
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have driverResponseContinuous : ContinuousOn driverResponse (Icc 0 finish) :=
    convolution_continuous_on_prefix finishNonnegative driverContinuous rate
  have remainingResponseContinuous : ContinuousOn remainingResponse (Icc 0 finish) :=
    convolution_continuous_on_prefix finishNonnegative remainingContinuous rate
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have weightedIntegrable (function : ℝ → ℝ) (regular : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) * function time) volume 0 finish :=
    (weightContinuous.continuousOn.mul regular).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have weightedEnvelope := weightedIntegrable envelope envelopeContinuous
  have weightedDriver := weightedIntegrable driver driverContinuous
  have weightedRemaining := weightedIntegrable remaining remainingContinuous
  have weightedReturned := weightedIntegrable returned returnedContinuous
  have weightedDriverResponse := weightedIntegrable driverResponse driverResponseContinuous
  have weightedRemainingResponse := weightedIntegrable remainingResponse remainingResponseContinuous
  let driverAction := ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * driver time
  let remainingAction := ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * remaining time
  let driverResponseAction := ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * driverResponse time
  let remainingResponseAction := ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * remainingResponse time
  have driverActionNonnegative : 0 ≤ driverAction := intervalIntegral.integral_nonneg_of_forall finishNonnegative
    (fun time => mul_nonneg (Real.exp_pos _).le (driverNonnegative time))
  have remainingActionNonnegative : 0 ≤ remainingAction := intervalIntegral.integral_nonneg_of_forall finishNonnegative
    (fun time => mul_nonneg (Real.exp_pos _).le (remainingNonnegative time))
  have driverConvolution : driverResponseAction ≤ driverAction / (weight - rate) :=
    EulerNonuniqueness.weighted_exponential_convolution_integral_le driverContinuous (sub_pos.mp gapPositive)
      finishNonnegative (fun time _ => driverNonnegative time)
  have remainingConvolution : remainingResponseAction ≤ remainingAction / (weight - rate) :=
    EulerNonuniqueness.weighted_exponential_convolution_integral_le remainingContinuous (sub_pos.mp gapPositive)
      finishNonnegative (fun time _ => remainingNonnegative time)
  have majorantIntegrable := ((weightedDriver.const_mul (constant * rho)).add
    (weightedRemainingResponse.const_mul (constant * rho))).add (weightedDriverResponse.const_mul (constant * rho ^ 2))
  have integrated := intervalIntegral.integral_mono_on finishNonnegative weightedReturned majorantIntegrable (by
    intro time inside
    have scaled := mul_le_mul_of_nonneg_left (pointwise time inside).2.2 (Real.exp_pos (-weight * time)).le
    convert scaled using 1; ring)
  rw [intervalIntegral.integral_add ((weightedDriver.const_mul (constant * rho)).add
      (weightedRemainingResponse.const_mul (constant * rho))) (weightedDriverResponse.const_mul (constant * rho ^ 2)),
    intervalIntegral.integral_add (weightedDriver.const_mul (constant * rho)) (weightedRemainingResponse.const_mul (constant * rho)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at integrated
  have convolved := add_le_add (add_le_add_left
    (mul_le_mul_of_nonneg_left remainingConvolution (mul_nonneg constantNonnegative rhoNonnegative)) (constant * rho * driverAction))
    (mul_le_mul_of_nonneg_left driverConvolution (mul_nonneg constantNonnegative (sq_nonneg rho)))
  have coefficientSmall : constant * rho + constant * rho ^ 2 / (weight - rate) ≤ tolerance := by
    have divided := (inverseBound (constant * rho ^ 2)
      (mul_nonneg constantNonnegative (sq_nonneg rho))).trans
        (div_le_self (by positivity : 0 ≤ 2 * (constant * rho ^ 2)) omegaOne)
    have comparison : constant * rho + constant * rho ^ 2 / (weight - rate) ≤
        constant * rho + 2 * constant * rho ^ 2 := by
      nlinarith only [divided]
    exact comparison.trans (le_of_lt absorptionSmall)
  have remainingCoefficient : constant * rho / (weight - rate) ≤
      2 * constant * rho / changed.omega (drive.val + 1) := by
    convert inverseBound (constant * rho) (mul_nonneg constantNonnegative rhoNonnegative) using 1; ring
  have coefficients := add_le_add (mul_le_mul_of_nonneg_right coefficientSmall driverActionNonnegative)
    (mul_le_mul_of_nonneg_right remainingCoefficient remainingActionNonnegative)
  refine ⟨envelopeContinuous, driverContinuous, remainingContinuous, returnedContinuous, driverResponseContinuous,
    remainingResponseContinuous, initialZero, slowRateBound, ⟨omegaPositive, gapBound⟩, weightedEnvelope, weightedDriver,
    weightedRemaining, weightedReturned, weightedDriverResponse, weightedRemainingResponse, ?_⟩
  apply integrated.trans
  apply le_trans convolved
  convert coefficients using 1; ring

end EulerNonuniqueness.Paper

