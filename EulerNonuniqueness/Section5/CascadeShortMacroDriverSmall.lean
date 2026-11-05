import EulerNonuniqueness.Section5.CascadeAdmissibleMacroSourceBound
import EulerNonuniqueness.Section5.CascadeCoarserFollowerRow
import EulerNonuniqueness.Section1.ExternalFieldScaleBounds

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_short_macro_driver_small :
    ∃ rawCap > (0 : ℝ),
    ∀ span multiplier row tolerance : ℝ, 0 ≤ span → 0 ≤ multiplier → 0 ≤ row → 0 < tolerance →
    ∀ scales : Scales, 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ start finish rate : ℝ,
    0 ≤ start → start ≤ finish → finish ≤ path.stop →
    let changed : Scales := {scales with frequency := frequency}
    changed.omega (index.val + 1) * (finish - start) ≤ span → rate ≤ changed.omega (index.val + 1) →
    let rho := 216360000 * changed.hessian + 576 * changed.strain
    let driver := fun time => Real.exp (rate * (finish - time)) * row * rho * prepared.weightedMacroSourceState time index
    ContinuousOn driver (Icc start finish) ∧
    IntervalIntegrable driver volume start finish ∧
    multiplier / changed.location (index.val + 1) ^ 4 * (∫ time in start..finish, driver time) ≤ tolerance := by
  obtain ⟨boundCap, boundPositive, constant, constantOne, bounds⟩ :=
    exists_uniform_actual_admissible_macro_source_bound
  obtain ⟨continuousCap, continuousPositive, continuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min boundCap continuousCap
  have capPositive : 0 < rawCap := lt_min boundPositive continuousPositive
  have capBound : rawCap ≤ boundCap := min_le_left _ _
  have capContinuous : rawCap ≤ continuousCap := min_le_right _ _
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantOne
  refine ⟨rawCap, capPositive, ?_⟩
  intro span multiplier row tolerance spanNonnegative multiplierNonnegative rowNonnegative tolerancePositive scales ratioBound alphaPositive
  let rhoAt := fun frequency : ℝ => 216360000 * ({scales with frequency := frequency}).hessian +
    576 * ({scales with frequency := frequency}).strain
  have rhoLimit : Tendsto rhoAt atTop (𝓝 0) := by
    simpa only [rhoAt, mul_zero, zero_add] using
      (((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576))
  let total := multiplier * Real.exp span * row * constant * span
  filter_upwards [rhoLimit.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (max 1 (total / tolerance))] with frequency rhoSmall frequencyLarge
  intro orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count
    prepared path index start finish rate startNonnegative ordered finishBound
  dsimp only
  intro durationBound rateBound
  let changed : Scales := {scales with frequency := frequency}
  let distance := changed.location (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let rho := rhoAt frequency
  let driver := fun time => Real.exp (rate * (finish - time)) * row * rho * prepared.weightedMacroSourceState time index
  have frequencyOne : 1 ≤ frequency := (le_max_left _ _).trans frequencyLarge
  have frequencyPositive : 0 < frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have distancePositive : 0 < distance := changed.location_pos _
  have rhoNonnegative : 0 ≤ rho := by
    have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun source =>
      div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
        (pow_nonneg (changed.location_pos _).le _)
    dsimp only [rho, rhoAt]
    positivity
  have rhoOne : rho ≤ 1 := rhoSmall.le
  have subset : Icc start finish ⊆ Icc 0 path.stop := Icc_subset_Icc startNonnegative finishBound
  have macroContinuous := (continuity prepared capPositive capContinuous path index).2.2.2.mono subset
  have weightedContinuous : ContinuousOn (fun time => prepared.weightedMacroSourceState time index) (Icc start finish) :=
    continuousOn_const.mul macroContinuous
  have driverContinuous : ContinuousOn driver (Icc start finish) :=
    (((by fun_prop : Continuous (fun time : ℝ => Real.exp (rate * (finish - time)))).continuousOn.mul continuousOn_const).mul continuousOn_const).mul weightedContinuous
  have driverI := driverContinuous.intervalIntegrable_of_Icc (μ := volume) ordered
  have macroBound (time : ℝ) (inside : time ∈ Icc start finish) :
      prepared.weightedMacroSourceState time index ≤ constant * distance ^ 3 := by
    have bound := bounds (prepared.enlargeCap capBound) path time (subset inside) index
    have invariant : (prepared.enlargeCap capBound).macroSourceState = prepared.macroSourceState := by
      funext time source
      with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
    rw [invariant] at bound
    have scaled := mul_le_mul_of_nonneg_left bound (pow_nonneg distancePositive.le 3)
    change distance ^ 4 * prepared.macroSourceState time index ≤ constant * distance ^ 3
    convert scaled using 1 <;> ring
  have pointBound (time : ℝ) (inside : time ∈ Icc start finish) :
      driver time ≤ Real.exp span * row * constant * distance ^ 3 := by
    have exponentBound : rate * (finish - time) ≤ span :=
      ((mul_le_mul_of_nonneg_right rateBound (sub_nonneg.mpr inside.2)).trans
        (mul_le_mul_of_nonneg_left (sub_le_sub_left inside.1 finish) omegaPositive.le)).trans durationBound
    have kernelBound := Real.exp_le_exp.mpr exponentBound
    have first := mul_le_mul_of_nonneg_left (macroBound time inside)
      (show 0 ≤ Real.exp (rate * (finish - time)) * row * rho by positivity)
    have second := mul_le_mul_of_nonneg_left rhoOne
      (show 0 ≤ Real.exp (rate * (finish - time)) * row * (constant * distance ^ 3) by positivity)
    have third := mul_le_mul_of_nonneg_right kernelBound
      (show 0 ≤ row * constant * distance ^ 3 by positivity)
    dsimp only [driver]
    nlinarith only [first, second, third]
  have integralBound := intervalIntegral.integral_mono_on ordered driverI (intervalIntegrable_const)
    pointBound
  rw [intervalIntegral.integral_const] at integralBound
  simp only [smul_eq_mul] at integralBound
  have frequencyDistance : frequency ≤ omega * distance := by
    have powers : (2 : ℝ) ^ (index.val + 1) ≤ scales.ratio ^ (index.val + 1) :=
      pow_le_pow_left₀ (by norm_num) ratioBound _
    have scaled := mul_le_mul_of_nonneg_left powers frequencyPositive.le
    dsimp only [omega, distance, changed, Scales.omega]
    rw [Scales.location_eq_inv_pow]
    apply (le_mul_inv_iff₀ (by positivity : 0 < (2 : ℝ) ^ (index.val + 1))).mpr
    simpa only [mul_comm] using scaled
  have short : (finish - start) / distance ≤ span / frequency := by
    apply (div_le_div_iff₀ distancePositive frequencyPositive).mpr
    have multiplied := mul_le_mul_of_nonneg_right frequencyDistance (sub_nonneg.mpr ordered)
    have capped := mul_le_mul_of_nonneg_right durationBound distancePositive.le
    nlinarith only [multiplied, capped]
  have coefficientNonnegative : 0 ≤ multiplier * Real.exp span * row * constant := by positivity
  have actionBound := mul_le_mul_of_nonneg_left integralBound
    (show 0 ≤ multiplier / distance ^ 4 by positivity)
  have shortBound := mul_le_mul_of_nonneg_left short coefficientNonnegative
  have frequencyThreshold : total / tolerance ≤ frequency := (le_max_right _ _).trans frequencyLarge
  have finalBound : total / frequency ≤ tolerance := by
    apply (div_le_iff₀ frequencyPositive).mpr
    have product := (div_le_iff₀ tolerancePositive).mp frequencyThreshold
    nlinarith only [product]
  refine ⟨driverContinuous, driverI, ?_⟩
  change multiplier / distance ^ 4 * (∫ time in start..finish, driver time) ≤ tolerance
  calc
    _ ≤ multiplier / distance ^ 4 * ((finish - start) * (Real.exp span * row * constant * distance ^ 3)) := actionBound
    _ = (multiplier * Real.exp span * row * constant) * ((finish - start) / distance) := by field_simp; ring
    _ ≤ (multiplier * Real.exp span * row * constant) * (span / frequency) := shortBound
    _ = total / frequency := by dsimp only [total]; ring
    _ ≤ tolerance := finalBound

end EulerNonuniqueness.Paper
