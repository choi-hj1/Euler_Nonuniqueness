import EulerNonuniqueness.Section5.CascadeFollowerReturnKernel
import EulerNonuniqueness.General.RetainedExponentialConvolution

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

private theorem follower_convolution_continuous {forcing : ℝ → ℝ} {finish : ℝ}
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

private theorem follower_original_convolution_split {forcing : ℝ → ℝ} {finish start time rate : ℝ}
    (regular : ContinuousOn forcing (Icc 0 finish)) (startNonnegative : 0 ≤ start)
    (ordered : start ≤ time) (timeBound : time ≤ finish) :
    (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current) =
      Real.exp (rate * (time - start)) *
        (∫ current in (0 : ℝ)..start, Real.exp (rate * (start - current)) * forcing current) +
          ∫ current in start..time, Real.exp (rate * (time - current)) * forcing current := by
  have firstRegular : ContinuousOn (fun current => Real.exp (rate * (time - current)) * forcing current) (Icc 0 start) :=
    (by fun_prop : Continuous (fun current : ℝ => Real.exp (rate * (time - current)))).continuousOn.mul
      (regular.mono (Icc_subset_Icc le_rfl (ordered.trans timeBound)))
  have secondRegular : ContinuousOn (fun current => Real.exp (rate * (time - current)) * forcing current) (Icc start time) :=
    (by fun_prop : Continuous (fun current : ℝ => Real.exp (rate * (time - current)))).continuousOn.mul
      (regular.mono (Icc_subset_Icc startNonnegative timeBound))
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (firstRegular.intervalIntegrable_of_Icc (μ := volume) startNonnegative)
    (secondRegular.intervalIntegrable_of_Icc (μ := volume) ordered)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro current _
  dsimp only
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem follower_retained_weighted_bound
    {driver remaining returned : ℝ → ℝ} {constant rho rate weight tolerance start finish : ℝ}
    (driverContinuous : ContinuousOn driver (Icc 0 finish))
    (remainingContinuous : ContinuousOn remaining (Icc 0 finish))
    (returnedContinuous : ContinuousOn returned (Icc 0 finish))
    (driverNonnegative : ∀ time, 0 ≤ driver time)
    (remainingNonnegative : ∀ time, 0 ≤ remaining time)
    (constantNonnegative : 0 ≤ constant) (rhoNonnegative : 0 ≤ rho)
    (weightOne : 1 ≤ weight) (slowRate : rate ≤ weight / 2)
    (absorption : constant * rho + 2 * constant * rho ^ 2 ≤ tolerance)
    (startNonnegative : 0 ≤ start) (ordered : start ≤ finish)
    (pointwise : ∀ time ∈ Icc 0 finish,
      returned time ≤ constant * rho * driver time +
        constant * rho * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * remaining current) +
        constant * rho ^ 2 * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current)) :
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * returned time) ≤
      (2 / weight) * (constant * rho * (∫ current in (0 : ℝ)..start,
        Real.exp (rate * (start - current)) * remaining current) +
          constant * rho ^ 2 * (∫ current in (0 : ℝ)..start,
            Real.exp (rate * (start - current)) * driver current)) +
      tolerance * (∫ time in start..finish, Real.exp (-weight * (time - start)) * driver time) +
      (2 * constant * rho / weight) *
        (∫ time in start..finish, Real.exp (-weight * (time - start)) * remaining time) := by
  have weightPositive : 0 < weight := zero_lt_one.trans_le weightOne
  have gapBound : weight / 2 ≤ weight - rate := by linarith only [slowRate]
  have gapPositive : 0 < weight - rate := (half_pos weightPositive).trans_le gapBound
  have driverEstimate := EulerNonuniqueness.weighted_retained_exponential_convolution_integral_le
    driverContinuous (fun time _ => driverNonnegative time) startNonnegative ordered (sub_pos.mp gapPositive)
  have remainingEstimate := EulerNonuniqueness.weighted_retained_exponential_convolution_integral_le
    remainingContinuous (fun time _ => remainingNonnegative time) startNonnegative ordered (sub_pos.mp gapPositive)
  let driverAction := ∫ time in start..finish, Real.exp (-weight * (time - start)) * driver time
  let remainingAction := ∫ time in start..finish, Real.exp (-weight * (time - start)) * remaining time
  let memory := constant * rho * (∫ current in (0 : ℝ)..start,
    Real.exp (rate * (start - current)) * remaining current) +
      constant * rho ^ 2 * (∫ current in (0 : ℝ)..start, Real.exp (rate * (start - current)) * driver current)
  have driverActionNonnegative : 0 ≤ driverAction := intervalIntegral.integral_nonneg_of_forall ordered
    (fun time => mul_nonneg (Real.exp_pos _).le (driverNonnegative time))
  have remainingActionNonnegative : 0 ≤ remainingAction := intervalIntegral.integral_nonneg_of_forall ordered
    (fun time => mul_nonneg (Real.exp_pos _).le (remainingNonnegative time))
  have memoryNonnegative : 0 ≤ memory := by
    have prefixNonnegative (forcing : ℝ → ℝ) (nonnegative : ∀ time, 0 ≤ forcing time) :
        0 ≤ ∫ current in (0 : ℝ)..start, Real.exp (rate * (start - current)) * forcing current :=
      intervalIntegral.integral_nonneg_of_forall startNonnegative
        (fun current => mul_nonneg (Real.exp_pos _).le (nonnegative current))
    exact add_nonneg (mul_nonneg (mul_nonneg constantNonnegative rhoNonnegative) (prefixNonnegative remaining remainingNonnegative))
      (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg rho)) (prefixNonnegative driver driverNonnegative))
  have inverseBound (numerator : ℝ) (nonnegative : 0 ≤ numerator) :
      numerator / (weight - rate) ≤ 2 * numerator / weight := by
    calc
      _ ≤ numerator / (weight / 2) := div_le_div_of_nonneg_left nonnegative (half_pos weightPositive) gapBound
      _ = _ := by rw [div_div_eq_mul_div]; ring
  have weightedReturned := ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-weight * (time - start)))).continuousOn.mul
    (returnedContinuous.mono (Icc_subset_Icc startNonnegative le_rfl))).intervalIntegrable_of_Icc (μ := volume) ordered
  have majorantIntegrable := ((driverEstimate.2.1.const_mul (constant * rho)).add
    (remainingEstimate.1.const_mul (constant * rho))).add (driverEstimate.1.const_mul (constant * rho ^ 2))
  have integrated := intervalIntegral.integral_mono_on ordered weightedReturned majorantIntegrable (by
    intro time inside
    convert mul_le_mul_of_nonneg_left (pointwise time ⟨startNonnegative.trans inside.1, inside.2⟩)
      (Real.exp_pos (-weight * (time - start))).le using 1; ring)
  rw [intervalIntegral.integral_add ((driverEstimate.2.1.const_mul (constant * rho)).add
      (remainingEstimate.1.const_mul (constant * rho))) (driverEstimate.1.const_mul (constant * rho ^ 2)),
    intervalIntegral.integral_add (driverEstimate.2.1.const_mul (constant * rho)) (remainingEstimate.1.const_mul (constant * rho)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at integrated
  have convolved := add_le_add (add_le_add_left
    (mul_le_mul_of_nonneg_left remainingEstimate.2.2 (mul_nonneg constantNonnegative rhoNonnegative))
      (constant * rho * driverAction))
    (mul_le_mul_of_nonneg_left driverEstimate.2.2 (mul_nonneg constantNonnegative (sq_nonneg rho)))
  have coefficientSmall : constant * rho + constant * rho ^ 2 / (weight - rate) ≤ tolerance := by
    have divided := (inverseBound (constant * rho ^ 2) (mul_nonneg constantNonnegative (sq_nonneg rho))).trans
      (div_le_self (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg constantNonnegative (sq_nonneg rho))) weightOne)
    nlinarith only [divided, absorption]
  have coefficients := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right coefficientSmall driverActionNonnegative)
    (mul_le_mul_of_nonneg_right (inverseBound (constant * rho) (mul_nonneg constantNonnegative rhoNonnegative)) remainingActionNonnegative))
    (inverseBound memory memoryNonnegative)
  apply integrated.trans
  apply le_trans convolved
  convert coefficients using 1 <;> dsimp only [memory, driverAction, remainingAction] <;> ring

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_follower_retained_window_return :
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
    let changed : Scales := {scales with frequency := frequency}
    let remaining := prepared.followerStrictlyFinerForcing drive
    let driver := fun time => prepared.weightedMacroSourceState time drive
    let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
    let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
    let memory := fun time => constant * rho * (∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * remaining current) +
        constant * rho ^ 2 * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current)
    ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    ContinuousOn returned (Icc 0 finish) ∧ ContinuousOn memory (Icc 0 finish) ∧
    memory 0 = 0 ∧ 0 ≤ rho ∧ 0 ≤ rate ∧ rate ≤ changed.omega (drive.val + 1) / 2 ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ driver time ∧ 0 ≤ remaining time ∧ 0 ≤ returned time ∧ 0 ≤ memory time) ∧
    ∀ start ∈ Icc 0 finish, ∀ time ∈ Icc start finish,
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * driver current) volume start time ∧
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * remaining current) volume start time ∧
      memory time = Real.exp (rate * (time - start)) * memory start +
        constant * rho * (∫ current in start..time, Real.exp (rate * (time - current)) * remaining current) +
        constant * rho ^ 2 * (∫ current in start..time, Real.exp (rate * (time - current)) * driver current) ∧
      returned time ≤ constant * rho * driver time + Real.exp (rate * (time - start)) * memory start +
        constant * rho * (∫ current in start..time, Real.exp (rate * (time - current)) * remaining current) +
        constant * rho ^ 2 * (∫ current in start..time, Real.exp (rate * (time - current)) * driver current) ∧
      ∀ weight : ℝ, changed.omega (drive.val + 1) ≤ weight →
        IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * returned current) volume start time ∧
        IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * driver current) volume start time ∧
        IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * remaining current) volume start time ∧
        IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * memory current) volume start time ∧
        (∫ current in start..time, Real.exp (-weight * (current - start)) * returned current) ≤
          (2 / weight) * memory start +
          tolerance * (∫ current in start..time, Real.exp (-weight * (current - start)) * driver current) +
          (2 * constant * rho / weight) *
            (∫ current in start..time, Real.exp (-weight * (current - start)) * remaining current) := by
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
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have parentRatio : max 2 (2 * constant) ≤ scales.ratio := by
    apply max_le ratioBound
    have bound := (le_max_right (2 : ℝ) (4 * constant)).trans ratioLarge
    linarith only [bound, constantOne]
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
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
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      (thresholdBound.trans thresholdEighth) referenceNonnegative rootOne boundaryOne factorPositive
        (by linarith only [factorSmall] : factor ≤ 1),
    absorptionDecay.eventually (eventually_lt_nhds tolerancePositive),
    feedbackDecay.eventually (by simpa only [mul_zero] using eventually_lt_nhds quarterPositive),
    eventually_ge_atTop (1 : ℝ)] with frequency returnedBound selectedContinuous absorptionSmall feedbackSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive driveNonterminal finish finishNonnegative finishBound small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let remaining := prepared.followerStrictlyFinerForcing drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let selected := Finset.univ.filter (fun source : Fin count => source.val < drive.val ∧ source ≠ drive)
  let returned := fun time => changed.location (drive.val + 1) ^ 4 * prepared.selectedForeignForcing selected drive time
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
  let memory := fun time => constant * rho * (∫ current in (0 : ℝ)..time,
    Real.exp (rate * (time - current)) * remaining current) +
      constant * rho ^ 2 * (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * driver current)
  obtain ⟨_, driverContinuous, remainingContinuous, returnedContinuous, _, _, _, _, _, _, _, pointwise⟩ :=
    returnedBound count phase dipoleAngle prepared path drive driveNonterminal finish finishNonnegative finishBound small
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
    exact add_nonneg (mul_nonneg (by norm_num) hessianNonnegative) (mul_nonneg (by norm_num) strainNonnegative)
  have rateNonnegative : 0 ≤ rate := add_nonneg
    (div_nonneg (mul_nonneg constantNonnegative omegaPositive.le) ratioPositive.le)
    (mul_nonneg constantNonnegative rhoNonnegative)
  have geometricQuarter : constant * changed.omega (drive.val + 1) / changed.ratio ≤
      changed.omega (drive.val + 1) / 4 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have separated : 4 * constant ≤ changed.ratio := (le_max_right _ _).trans ratioLarge
    have comparison := mul_le_mul_of_nonneg_right separated omegaPositive.le
    nlinarith only [comparison]
  have slowRate : rate ≤ changed.omega (drive.val + 1) / 2 := by
    have feedbackQuarter : constant * rho ≤ 1 / 4 := le_of_lt feedbackSmall
    dsimp only [rate]
    linarith only [geometricQuarter, feedbackQuarter, omegaOne]
  have driverNonnegative (time : ℝ) : 0 ≤ driver time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4) (prepared.macroSourceState_nonnegative time drive)
  have remainingNonnegative (time : ℝ) : 0 ≤ remaining time := norm_nonneg _
  have selectedSubset : selected ⊆ Finset.univ.erase drive := by
    intro source member
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp member).2.2, Finset.mem_univ _⟩
  have returnedNonnegative (time : ℝ) : 0 ≤ returned time :=
    mul_nonneg (pow_nonneg (changed.location_pos _).le 4)
      ((selectedContinuous count phase dipoleAngle prepared path drive selected selectedSubset).1 time)
  have driverResponseContinuous := follower_convolution_continuous finishNonnegative driverContinuous rate
  have remainingResponseContinuous := follower_convolution_continuous finishNonnegative remainingContinuous rate
  have memoryContinuous : ContinuousOn memory (Icc 0 finish) :=
    (continuousOn_const.mul remainingResponseContinuous).add (continuousOn_const.mul driverResponseContinuous)
  have memoryNonnegative (time : ℝ) (inside : time ∈ Icc 0 finish) : 0 ≤ memory time :=
    add_nonneg (mul_nonneg (mul_nonneg constantNonnegative rhoNonnegative)
      (intervalIntegral.integral_nonneg_of_forall inside.1 (fun current =>
        mul_nonneg (Real.exp_pos _).le (remainingNonnegative current))))
      (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg rho))
        (intervalIntegral.integral_nonneg_of_forall inside.1 (fun current =>
          mul_nonneg (Real.exp_pos _).le (driverNonnegative current))))
  refine ⟨driverContinuous, remainingContinuous, returnedContinuous, memoryContinuous,
    by simp only [memory, intervalIntegral.integral_same, mul_zero, add_zero], rhoNonnegative,
    rateNonnegative, slowRate, (fun time inside => ⟨driverNonnegative time, remainingNonnegative time,
      returnedNonnegative time, memoryNonnegative time inside⟩), ?_⟩
  intro start startInside time timeInside
  have subset : Icc start time ⊆ Icc 0 finish := Icc_subset_Icc startInside.1 timeInside.2
  have driverKernel := ((by fun_prop : Continuous (fun current : ℝ => Real.exp (rate * (time - current)))).continuousOn.mul
    (driverContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) timeInside.1
  have remainingKernel := ((by fun_prop : Continuous (fun current : ℝ => Real.exp (rate * (time - current)))).continuousOn.mul
    (remainingContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) timeInside.1
  have memorySplit : memory time = Real.exp (rate * (time - start)) * memory start +
      constant * rho * (∫ current in start..time, Real.exp (rate * (time - current)) * remaining current) +
      constant * rho ^ 2 * (∫ current in start..time, Real.exp (rate * (time - current)) * driver current) := by
    dsimp only [memory]
    rw [follower_original_convolution_split remainingContinuous startInside.1 timeInside.1 timeInside.2,
      follower_original_convolution_split driverContinuous startInside.1 timeInside.1 timeInside.2]
    ring
  have returnedPointwise := (pointwise time ⟨startInside.1.trans timeInside.1, timeInside.2⟩).2.2
  have retainedPointwise : returned time ≤ constant * rho * driver time + Real.exp (rate * (time - start)) * memory start +
      constant * rho * (∫ current in start..time, Real.exp (rate * (time - current)) * remaining current) +
      constant * rho ^ 2 * (∫ current in start..time, Real.exp (rate * (time - current)) * driver current) := by
    calc
      returned time ≤ constant * rho * driver time + memory time := by
        convert returnedPointwise using 1; dsimp only [memory]; ring
      _ = _ := by rw [memorySplit]; ring
  refine ⟨driverKernel, remainingKernel, memorySplit, retainedPointwise, ?_⟩
  intro weight weightBound
  have weightedIntegrable (function : ℝ → ℝ) (regular : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun current => Real.exp (-weight * (current - start)) * function current) volume start time :=
    ((by fun_prop : Continuous (fun current : ℝ => Real.exp (-weight * (current - start)))).continuousOn.mul
      (regular.mono subset)).intervalIntegrable_of_Icc (μ := volume) timeInside.1
  refine ⟨weightedIntegrable returned returnedContinuous, weightedIntegrable driver driverContinuous,
    weightedIntegrable remaining remainingContinuous, weightedIntegrable memory memoryContinuous, ?_⟩
  exact follower_retained_weighted_bound
    (driverContinuous.mono (Icc_subset_Icc le_rfl timeInside.2))
    (remainingContinuous.mono (Icc_subset_Icc le_rfl timeInside.2))
    (returnedContinuous.mono (Icc_subset_Icc le_rfl timeInside.2))
    driverNonnegative remainingNonnegative constantNonnegative rhoNonnegative (omegaOne.trans weightBound)
    (slowRate.trans (div_le_div_of_nonneg_right weightBound (by norm_num))) (le_of_lt absorptionSmall)
    startInside.1 timeInside.1 (fun current inside =>
      (pointwise current ⟨inside.1, inside.2.trans timeInside.2⟩).2.2)

end EulerNonuniqueness.Paper
