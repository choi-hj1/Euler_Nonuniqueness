import EulerNonuniqueness.General.StrictPrefixBootstrap
import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem integral_exp_neg_mul_le_of_same_rate_majorant
    {function : ℝ → ℝ} {finish origin rate bound : ℝ}
    (finishNonnegative : 0 ≤ finish)
    (integrable : IntervalIntegrable (fun time => Real.exp (-rate * time) * function time) volume 0 finish)
    (majorized : ∀ time ∈ Icc 0 finish, function time ≤ bound * Real.exp (rate * (time - origin))) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * function time) ≤
      finish * bound * Real.exp (-rate * origin) := by
  have comparison := integral_mono_on finishNonnegative integrable
    (intervalIntegrable_const (bound * Real.exp (-rate * origin)) :
      IntervalIntegrable (fun _ : ℝ => bound * Real.exp (-rate * origin)) volume 0 finish)
    (by
      intro time inside
      apply (mul_le_mul_of_nonneg_left (majorized time inside) (Real.exp_pos _).le).trans_eq
      calc
        _ = bound * (Real.exp (-rate * time) * Real.exp (rate * (time - origin))) := by ring
        _ = _ := by
          rw [← Real.exp_add, show -rate * time + rate * (time - origin) = -rate * origin by ring])
  simpa only [integral_const, sub_zero, smul_eq_mul, mul_assoc] using comparison

end intervalIntegral

namespace EulerNonuniqueness.General

theorem exponential_profile_le_of_small_action
    {value integral bound stableConstant cost finish origin rate : ℝ}
    (stablePositive : 0 < stableConstant) (boundNonnegative : 0 ≤ bound)
    (costSmall : cost ≤ Real.log 2 / (2 * stableConstant))
    (response : Real.exp (-rate * finish) * value ≤
      2 * Real.exp (2 * stableConstant * cost) * integral)
    (integralBound : integral ≤ bound * Real.exp (-rate * origin)) :
    value ≤ 4 * bound * Real.exp (rate * (finish - origin)) := by
  have exponentBound : 2 * stableConstant * cost ≤ Real.log 2 := by
    nlinarith only [(le_div_iff₀ (by positivity : 0 < 2 * stableConstant)).mp costSmall]
  have exponentialBound : Real.exp (2 * stableConstant * cost) ≤ 2 := by
    exact (Real.exp_le_exp.mpr exponentBound).trans_eq (Real.exp_log (by norm_num))
  have bounded := response.trans (mul_le_mul_of_nonneg_left integralBound
    (by positivity : 0 ≤ 2 * Real.exp (2 * stableConstant * cost)))
  have reduced : Real.exp (-rate * finish) * value ≤ 4 * bound * Real.exp (-rate * origin) := by
    apply bounded.trans
    nlinarith only [mul_le_mul_of_nonneg_right exponentialBound
      (mul_nonneg boundNonnegative (Real.exp_pos (-rate * origin)).le)]
  have multiplied := mul_le_mul_of_nonneg_left reduced (Real.exp_pos (rate * finish)).le
  have cancellation : Real.exp (rate * finish) * Real.exp (-rate * finish) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have identity : Real.exp (rate * finish) * Real.exp (-rate * origin) =
      Real.exp (rate * (finish - origin)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    value = Real.exp (rate * finish) * (Real.exp (-rate * finish) * value) := by
      rw [← mul_assoc, cancellation, one_mul]
    _ ≤ Real.exp (rate * finish) * (4 * bound * Real.exp (-rate * origin)) := multiplied
    _ = (4 * bound) * (Real.exp (rate * finish) * Real.exp (-rate * origin)) := by ring
    _ = _ := by rw [identity]

theorem weighted_drive_bound_of_state_profile
    {state leading additive drive : ℝ → ℝ}
    {finish origin rate seed magnitude profileConstant stateSource leadingSource additiveSource accuracy eta : ℝ}
    (finishNonnegative : 0 ≤ finish) (finishOne : finish ≤ 1)
    (seedNonnegative : 0 ≤ seed) (magnitudeNonnegative : 0 ≤ magnitude)
    (profileNonnegative : 0 ≤ profileConstant) (stateSourceNonnegative : 0 ≤ stateSource)
    (accuracyNonnegative : 0 ≤ accuracy)
    (stateIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) * state time) volume 0 finish)
    (leadingIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) * leading time) volume 0 finish)
    (additiveIntegrable : IntervalIntegrable (fun time => Real.exp (-rate * time) * additive time) volume 0 finish)
    (driveIdentity : ∀ time ∈ Icc 0 finish, drive time = leading time + additive time)
    (stateProfile : ∀ time ∈ Icc 0 finish, state time ≤
      profileConstant * (2 * magnitude + stateSource) * seed * Real.exp (rate * (time - origin)))
    (leadingBound : (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * leading time) ≤
      (eta * magnitude + leadingSource) * seed * Real.exp (-rate * origin))
    (additiveBound : (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * additive time) ≤
      accuracy * (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * state time) +
        (accuracy / 3) * additiveSource * seed * Real.exp (-rate * origin)) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * drive time) ≤
      ((eta + 2 * accuracy * profileConstant) * magnitude + leadingSource +
        accuracy * profileConstant * stateSource + (accuracy / 3) * additiveSource) *
          seed * Real.exp (-rate * origin) := by
  have stateBound := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant
    finishNonnegative stateIntegrable stateProfile
  have constantNonnegative : 0 ≤ profileConstant * (2 * magnitude + stateSource) * seed * Real.exp (-rate * origin) := by
    positivity
  have stateReduced : (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * state time) ≤
      profileConstant * (2 * magnitude + stateSource) * seed * Real.exp (-rate * origin) := by
    apply stateBound.trans
    convert mul_le_mul_of_nonneg_right finishOne constantNonnegative using 1 <;> ring
  have additiveReduced := additiveBound.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left stateReduced accuracyNonnegative) _)
  have driveSplit : (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * drive time) =
      (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * leading time) +
        ∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * additive time := by
    rw [← intervalIntegral.integral_add leadingIntegrable additiveIntegrable]
    apply intervalIntegral.integral_congr
    intro time inside
    change Real.exp (-rate * time) * drive time =
      Real.exp (-rate * time) * leading time + Real.exp (-rate * time) * additive time
    rw [driveIdentity time (by simpa only [uIcc_of_le finishNonnegative] using inside), mul_add]
  rw [driveSplit]
  convert add_le_add leadingBound additiveReduced using 1; ring

theorem exponential_profile_of_prefix_half_improvement
    {function : ℝ → ℝ} {horizon origin rate magnitude seed : ℝ}
    (continuous : ContinuousOn function (Icc 0 horizon)) (initial : function 0 = 0)
    (magnitudePositive : 0 < magnitude) (seedPositive : 0 < seed)
    (improve : ∀ finish ∈ Icc 0 horizon,
      (∀ time ∈ Icc 0 finish, function time ≤ magnitude * seed * Real.exp (rate * (time - origin))) →
      function finish ≤ (magnitude / 2) * seed * Real.exp (rate * (finish - origin))) :
    ∀ time ∈ Icc 0 horizon,
      function time < magnitude * seed * Real.exp (rate * (time - origin)) ∧
      function time ≤ (magnitude / 2) * seed * Real.exp (rate * (time - origin)) := by
  let monitor := fun time => function time - magnitude * seed * Real.exp (rate * (time - origin))
  have exponentialContinuous : Continuous (fun time : ℝ => magnitude * seed * Real.exp (rate * (time - origin))) := by
    fun_prop
  have monitorContinuous : ContinuousOn monitor (Icc 0 horizon) := continuous.sub exponentialContinuous.continuousOn
  have monitorInitial : monitor 0 < 0 := by
    dsimp only [monitor]
    rw [initial]
    have positive : 0 < magnitude * seed * Real.exp (rate * (0 - origin)) := by positivity
    linarith only [positive]
  have strict := strictly_negative_of_strict_prefix_improvement monitorContinuous monitorInitial (by
    intro finish inside closed _
    have improved := improve finish inside (by
      intro time timeInside
      have bounded := closed time timeInside
      dsimp only [monitor] at bounded
      linarith only [bounded])
    have positive : 0 < magnitude * seed * Real.exp (rate * (finish - origin)) := by positivity
    dsimp only [monitor]
    nlinarith only [improved, positive])
  intro time inside
  have strictAt := strict time inside
  dsimp only [monitor] at strictAt
  exact ⟨by linarith only [strictAt], improve time inside (by
    intro current currentInside
    have strictBefore := strict current ⟨currentInside.1, currentInside.2.trans inside.2⟩
    dsimp only [monitor] at strictBefore
    linarith only [strictBefore])⟩

end EulerNonuniqueness.General
