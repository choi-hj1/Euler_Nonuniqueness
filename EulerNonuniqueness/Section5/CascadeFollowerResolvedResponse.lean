import EulerNonuniqueness.Section5.CascadeFollowerDrivenEnvelopeVolterra
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_follower_resolved_response :
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
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let resolvedRate := constant * changed.omega (drive.val + 1) / changed.ratio + constant * rho
    ContinuousOn envelope (Icc 0 finish) ∧ ContinuousOn driver (Icc 0 finish) ∧ ContinuousOn remaining (Icc 0 finish) ∧
    IntervalIntegrable envelope volume 0 finish ∧ IntervalIntegrable driver volume 0 finish ∧ IntervalIntegrable remaining volume 0 finish ∧
    envelope 0 = 0 ∧ resolvedRate ≤ changed.omega (drive.val + 1) ∧
    changed.omega (drive.val + 1) < 2 * Real.sqrt 2 * changed.omega (drive.val + 1) ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => Real.exp (resolvedRate * (time - current)) *
        (rho * driver current + remaining current)) volume 0 time ∧
      envelope time ≤ constant * ∫ current in (0 : ℝ)..time,
        Real.exp (resolvedRate * (time - current)) * (rho * driver current + remaining current) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, factory⟩ :=
    exists_uniform_actual_follower_driven_envelope_volterra
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, responses⟩ :=
    factory factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant boundaryConstant
    thresholdBound referenceNonnegative boundaryOne orbit sectionTime
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have constantNonnegative : 0 ≤ constant := zero_le_one.trans constantOne
  have feedbackDecay : Tendsto (fun frequency : ℝ => constant *
      (216360000 * ({scales with frequency := frequency}).hessian +
        576 * ({scales with frequency := frequency}).strain)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)).const_mul constant
  filter_upwards [responses scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive threshold referenceConstant
      boundaryConstant thresholdBound referenceNonnegative boundaryOne orbit sectionTime,
    feedbackDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    eventually_ge_atTop (1 : ℝ)] with frequency response feedbackSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path drive driveNonterminal finish finishNonnegative finishBound small
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let envelope := prepared.coarserFollowerEnvelope drive
  let remaining := prepared.followerStrictlyFinerForcing drive
  let driver := fun time => prepared.weightedMacroSourceState time drive
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let growth := constant * changed.omega (drive.val + 1) / changed.ratio
  let resolvedRate := growth + constant * rho
  let forcing := fun time => rho * driver time + remaining time
  have actual := response count phase dipoleAngle prepared path drive driveNonterminal finish finishNonnegative finishBound small
  obtain ⟨envelopeContinuous, driverContinuous, remainingContinuous, envelopeIntegrable, driverIntegrable,
    remainingIntegrable, initialZero, history⟩ := actual
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
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) :=
    (continuousOn_const.mul driverContinuous).add remainingContinuous
  have baseInequality : ∀ time ∈ Icc 0 finish, envelope time ≤ (0 : ℝ) * Real.exp (growth * time) +
      constant * ∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (forcing current + rho * envelope current) := by
    intro time inside
    have integralIdentity : (∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (rho * (envelope current + driver current) + remaining current)) =
        ∫ current in (0 : ℝ)..time,
          Real.exp (growth * (time - current)) * (forcing current + rho * envelope current) := by
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [forcing]
      ring
    have estimate := (history time inside).2
    rw [integralIdentity] at estimate
    simpa only [zero_mul, zero_add] using estimate
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall envelopeContinuous forcingContinuous
    rhoNonnegative constantNonnegative finishNonnegative baseInequality
  have halfRate : growth ≤ changed.omega (drive.val + 1) / 2 := by
    apply (div_le_iff₀ ratioPositive).mpr
    have separated : 2 * constant ≤ changed.ratio := (le_max_right _ _).trans ratioLarge
    have comparison := mul_le_mul_of_nonneg_right separated omegaPositive.le
    nlinarith only [comparison]
  have feedbackHalf : constant * rho ≤ 1 / 2 := le_of_lt feedbackSmall
  have rateBound : resolvedRate ≤ changed.omega (drive.val + 1) := by
    calc
      resolvedRate ≤ changed.omega (drive.val + 1) / 2 + 1 / 2 := add_le_add halfRate feedbackHalf
      _ ≤ changed.omega (drive.val + 1) / 2 + changed.omega (drive.val + 1) / 2 :=
        add_le_add_left (div_le_div_of_nonneg_right omegaOne (by norm_num : (0 : ℝ) ≤ 2)) _
      _ = changed.omega (drive.val + 1) := by ring
  have unstableGap : changed.omega (drive.val + 1) < 2 * Real.sqrt 2 * changed.omega (drive.val + 1) := by
    have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
    have comparison := mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le
    nlinarith only [comparison, omegaPositive]
  refine ⟨envelopeContinuous, driverContinuous, remainingContinuous, envelopeIntegrable, driverIntegrable,
    remainingIntegrable, initialZero, rateBound, unstableGap, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : Continuous (fun current : ℝ => Real.exp (resolvedRate * (time - current))) := by fun_prop
  refine ⟨(kernelContinuous.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1, ?_⟩
  simpa only [zero_mul, zero_add] using resolved time inside

end EulerNonuniqueness.Paper
