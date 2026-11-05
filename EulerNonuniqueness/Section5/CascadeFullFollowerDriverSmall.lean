import EulerNonuniqueness.Section5.CascadeCoarserFollowerRow
import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.Delay
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds
import EulerNonuniqueness.Section1.UniformInitialScaleSmallness
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem current_profile_convolution_le
    {function : ℝ → ℝ} {finish origin rate growth omega magnitude seed : ℝ}
    (regular : ContinuousOn function (Icc 0 finish)) (finishNonnegative : 0 ≤ finish)
    (omegaPositive : 0 < omega) (gap : omega ≤ growth - rate)
    (magnitudeNonnegative : 0 ≤ magnitude) (seedNonnegative : 0 ≤ seed)
    (profile : ∀ time ∈ Icc 0 finish,
      function time ≤ 4 * magnitude * seed * Real.exp (growth * (time - origin)))
    (exposure : seed * Real.exp (growth * (finish - origin)) ≤ 1) :
    (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * function time) ≤
      4 * magnitude / omega := by
  have ordered : rate < growth := by linarith only [gap, omegaPositive]
  have gapPositive : 0 < growth - rate := sub_pos.mpr ordered
  have weightedI := (((by fun_prop : Continuous (fun time : ℝ => Real.exp (-rate * time)))).continuousOn.mul
    regular).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have faster := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant finishNonnegative ordered
    (show 0 ≤ 4 * magnitude * seed by positivity) weightedI profile
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * function time) =
      Real.exp (rate * finish) * ∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * function time := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [identity]
  have first : Real.exp (rate * finish) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * function time) ≤
      (4 * magnitude / (growth - rate)) * (seed * Real.exp (growth * (finish - origin))) := by
    convert faster using 1
    ring
  have second := mul_le_mul_of_nonneg_left exposure
    (by positivity : 0 ≤ 4 * magnitude / (growth - rate))
  exact first.trans (second.trans (by
    simpa only [mul_one] using div_le_div_of_nonneg_left
      (by positivity : 0 ≤ 4 * magnitude) omegaPositive gap))

theorem exists_uniform_actual_full_follower_driver_small :
    ∃ rawCap > (0 : ℝ),
    ∀ magnitude multiplier row : ℝ, 0 ≤ magnitude → 0 ≤ multiplier → 0 ≤ row →
    ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant : ℝ),
    0 < factor → factor ≤ 1 / 100 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ {threshold referenceConstant : ℝ}, threshold ≤ 1 / 8 → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair, ∀ index : Fin count,
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop → ∀ origin rate : ℝ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let omega := changed.omega (index.val + 1)
    let location := changed.location (index.val + 1)
    let growth := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (index.val + 1)
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let driver := fun time => prepared.weightedMacroSourceState time index
    0 ≤ rate → rate ≤ growth / 4 →
    (∀ time ∈ Icc 0 finish,
      prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / location +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch ≤
          magnitude * seed * Real.exp (growth * (time - origin))) →
    seed * Real.exp (growth * (finish - origin)) ≤ 1 →
    ContinuousOn driver (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * row * rho * driver time) volume 0 finish ∧
    multiplier / location ^ 4 *
        (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * row * rho * driver time) ≤
      4 * multiplier * row * magnitude * rho / omega ∧
    multiplier / location ^ 4 *
        (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * row * rho * driver time) ≤ tolerance := by
  obtain ⟨rawCap, capPositive, states⟩ := exists_uniform_actual_source_state_continuity
  refine ⟨rawCap, capPositive, ?_⟩
  intro magnitude multiplier row magnitudeNonnegative multiplierNonnegative rowNonnegative tolerance tolerancePositive
    scales amplitudePositive ratioBound alphaPositive orbit sectionTime factor scaleRoot boundaryConstant factorPositive factorSmall
    rootOne boundaryOne threshold referenceConstant thresholdSmall referenceNonnegative
  let constant := 4 * multiplier * row * magnitude
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  let rhoAt := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency} : Scales).hessian +
    576 * ({scales with frequency := frequency} : Scales).strain
  have rhoLimit : Tendsto rhoAt atTop (𝓝 0) := by
    simpa only [rhoAt, mul_zero, zero_add] using
      ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  filter_upwards [scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    rhoLimit.eventually (eventually_lt_nhds zero_lt_one),
    eventually_ge_atTop (constant / tolerance + 1)] with frequency lengths rhoSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound origin rate
  dsimp only
  intro rateNonnegative rateBound profile exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let location := changed.location (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (index.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let macroState := fun time => prepared.macroSourceState time index
  let driver := fun time => prepared.weightedMacroSourceState time index
  have frequencyPositive : 0 < frequency := by
    have := div_nonneg constantNonnegative tolerancePositive.le
    linarith only [frequencyLarge, this]
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaLower : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _
  have locationPositive : 0 < location := changed.location_pos _
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have rhoNonnegative : 0 ≤ rho := by
    have hessian : 0 ≤ changed.hessian := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3)
    have strain : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    dsimp only [rho]
    positivity
  have gap : omega ≤ growth - rate := by
    have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    have growthLower : 2 * omega ≤ growth := by
      dsimp only [growth]
      nlinarith only [mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le]
    change rate ≤ growth / 4 at rateBound
    linarith only [rateBound, growthLower, omegaPositive]
  have macroContinuous : ContinuousOn macroState (Icc 0 finish) :=
    (states prepared capPositive le_rfl path index).2.2.2.mono (Icc_subset_Icc le_rfl finishBound)
  have driverContinuous : ContinuousOn driver (Icc 0 finish) := by
    exact continuousOn_const.mul macroContinuous
  have macroBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      macroState time ≤ 4 * magnitude * seed * Real.exp (growth * (time - origin)) := by
    have actual := prepared.macroSourceState_le_centered_and_raw path ⟨inside.1, inside.2.trans finishBound⟩ index
    rw [← prepared.referenceIdentity, norm_sub_rev] at actual
    have lengthRatio : changed.length (index.val + 1) / location ≤ 1 :=
      (div_le_one locationPositive).mpr (by simpa only [one_mul] using (lengths (index.val + 1)).le)
    have centeredNonnegative : 0 ≤ prepared.rawSourceCenteredState time index := div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
      apply Finset.sum_nonneg
      intro patch _
      dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
      positivity
    have centerNonnegative := div_nonneg (norm_nonneg (quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index)) locationPositive.le
    have momentNonnegative := norm_nonneg (relativeNormalizedFirstMoment changed motion prepared.reference index time)
    have centeredScaled := mul_le_mul_of_nonneg_right lengthRatio (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) centeredNonnegative)
    have sharp := profile time inside
    nlinarith only [actual, centeredScaled, sharp, rawNonnegative, centerNonnegative, momentNonnegative]
  have macroKernel := current_profile_convolution_le macroContinuous finishNonnegative omegaPositive gap
    magnitudeNonnegative seedPositive.le macroBound exposure
  have forcingContinuous : ContinuousOn (fun time => Real.exp (rate * (finish - time)) * row * rho * driver time)
      (Icc 0 finish) := by
    exact (((by fun_prop : Continuous (fun time : ℝ => Real.exp (rate * (finish - time))))).continuousOn.mul
      continuousOn_const |>.mul continuousOn_const).mul driverContinuous
  have normalizedIdentity : multiplier / location ^ 4 *
      (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * row * rho * driver time) =
      multiplier * row * rho * (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * macroState time) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only [driver, CascadeSourcePreparedPair.weightedMacroSourceState, macroState, location]
    field_simp
    ring
  have quantitative : multiplier / location ^ 4 *
      (∫ time in (0 : ℝ)..finish, Real.exp (rate * (finish - time)) * row * rho * driver time) ≤
      4 * multiplier * row * magnitude * rho / omega := by
    rw [normalizedIdentity]
    convert mul_le_mul_of_nonneg_left macroKernel (by positivity : 0 ≤ multiplier * row * rho) using 1
    ring
  have small : 4 * multiplier * row * magnitude * rho / omega ≤ tolerance := by
    have first := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left rhoSmall.le constantNonnegative) omegaPositive.le
    change constant * rho / omega ≤ constant * 1 / omega at first
    simp only [mul_one] at first
    have second := div_le_div_of_nonneg_left constantNonnegative frequencyPositive omegaLower
    have last : constant / frequency ≤ tolerance := (div_le_iff₀ frequencyPositive).mpr (by
      have lower := (div_le_iff₀ tolerancePositive).mp (show constant / tolerance ≤ frequency by linarith only [frequencyLarge])
      nlinarith only [lower])
    simpa only [constant, mul_one] using first.trans (second.trans last)
  exact ⟨driverContinuous, forcingContinuous.intervalIntegrable_of_Icc finishNonnegative, quantitative, quantitative.trans small⟩

end EulerNonuniqueness.Paper
