import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem exponential_nested_history_action_on_Icc
    {moment dilation stable momentForcing dilationForcing : ℝ → ℝ}
    {finish origin rate forcingConstant omega referenceSize : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (forcingNonnegative : 0 ≤ forcingConstant) (omegaNonnegative : 0 ≤ omega)
    (_momentContinuous : ContinuousOn moment (Icc 0 finish))
    (dilationContinuous : ContinuousOn dilation (Icc 0 finish))
    (stableContinuous : ContinuousOn stable (Icc 0 finish))
    (momentIntegrable : IntervalIntegrable momentForcing volume 0 finish)
    (dilationIntegrable : IntervalIntegrable (fun time => moment time + dilationForcing time) volume 0 finish)
    (momentHistory : ∀ time ∈ Icc 0 finish,
      moment time ≤ ∫ current in (0 : ℝ)..time, momentForcing current)
    (dilationHistory : ∀ time ∈ Icc 0 finish,
      dilation time ≤ ∫ current in (0 : ℝ)..time, moment current + dilationForcing current)
    (momentBound : ∀ time ∈ Icc 0 finish,
      momentForcing time ≤ forcingConstant * Real.exp (rate * (time - origin)))
    (dilationBound : ∀ time ∈ Icc 0 finish,
      dilationForcing time ≤ forcingConstant * Real.exp (rate * (time - origin))) :
    (∀ time ∈ Icc 0 finish,
      moment time ≤ forcingConstant / rate * Real.exp (rate * (time - origin)) ∧
      dilation time ≤ forcingConstant * (1 / rate + 1 / rate ^ 2) * Real.exp (rate * (time - origin))) ∧
    ContinuousOn (fun time => referenceSize + dilation time + |stable time|) (Icc 0 finish) ∧
    IntervalIntegrable (fun time => referenceSize + dilation time + |stable time|) volume 0 finish ∧
    IntervalIntegrable (fun time => |stable time|) volume 0 finish ∧
    omega * (∫ time in (0 : ℝ)..finish, referenceSize + dilation time + |stable time|) ≤
      omega * referenceSize * finish + omega * (∫ time in (0 : ℝ)..finish, |stable time|) +
        omega * forcingConstant * (1 / rate ^ 2 + 1 / rate ^ 3) * Real.exp (rate * (finish - origin)) := by
  have exponentialContinuous (constant : ℝ) :
      Continuous (fun time : ℝ => constant * Real.exp (rate * (time - origin))) := by fun_prop
  have exponentialIntegral (constant : ℝ) (constantNonnegative : 0 ≤ constant) (time : ℝ) :
      (∫ current in (0 : ℝ)..time, constant * Real.exp (rate * (current - origin))) ≤
        constant / rate * Real.exp (rate * (time - origin)) := by
    have derivative (current : ℝ) : HasDerivAt
        (fun next : ℝ => constant * Real.exp (rate * (next - origin)) / rate)
        (constant * Real.exp (rate * (current - origin))) current := by
      convert (((((hasDerivAt_id current).sub_const origin).const_mul rate).exp).const_mul constant).div_const rate using 1
      field_simp [ratePositive.ne']
      ring
    have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun current _ => derivative current)
      ((exponentialContinuous constant).intervalIntegrable 0 time)
    rw [identity]
    have initialNonnegative : 0 ≤ constant * Real.exp (rate * (0 - origin)) / rate := by positivity
    exact (sub_le_self _ initialNonnegative).trans_eq (by ring)
  have subinterval (time : ℝ) (inside : time ∈ Icc 0 finish) : uIcc 0 time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact Icc_subset_Icc le_rfl inside.2
  have momentEstimate (time : ℝ) (inside : time ∈ Icc 0 finish) :
      moment time ≤ forcingConstant / rate * Real.exp (rate * (time - origin)) := by
    have comparison := intervalIntegral.integral_mono_on inside.1
      (momentIntegrable.mono_set (subinterval time inside))
      ((exponentialContinuous forcingConstant).intervalIntegrable 0 time)
      (fun current member => momentBound current ⟨member.1, member.2.trans inside.2⟩)
    exact (momentHistory time inside).trans (comparison.trans (exponentialIntegral forcingConstant forcingNonnegative time))
  have dilationEstimate (time : ℝ) (inside : time ∈ Icc 0 finish) :
      dilation time ≤ forcingConstant * (1 / rate + 1 / rate ^ 2) * Real.exp (rate * (time - origin)) := by
    have comparison := intervalIntegral.integral_mono_on inside.1
      (dilationIntegrable.mono_set (subinterval time inside))
      ((exponentialContinuous (forcingConstant * (1 + 1 / rate))).intervalIntegrable 0 time) (by
        intro current member
        have actualInside : current ∈ Icc 0 finish := ⟨member.1, member.2.trans inside.2⟩
        have combined := add_le_add (momentEstimate current actualInside) (dilationBound current actualInside)
        exact combined.trans_eq (by ring))
    have integrated := exponentialIntegral (forcingConstant * (1 + 1 / rate)) (by positivity) time
    refine (dilationHistory time inside).trans (comparison.trans (integrated.trans_eq ?_))
    field_simp [ratePositive.ne']
    ring
  have dilationIntegralBound :
      (∫ time in (0 : ℝ)..finish, dilation time) ≤
        forcingConstant * (1 / rate ^ 2 + 1 / rate ^ 3) * Real.exp (rate * (finish - origin)) := by
    have comparison := intervalIntegral.integral_mono_on finishNonnegative
      (dilationContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
      ((exponentialContinuous (forcingConstant * (1 / rate + 1 / rate ^ 2))).intervalIntegrable 0 finish)
      dilationEstimate
    have integrated := exponentialIntegral (forcingConstant * (1 / rate + 1 / rate ^ 2)) (by positivity) finish
    refine comparison.trans (integrated.trans_eq ?_)
    field_simp [ratePositive.ne']
    ring
  have coefficientContinuous : ContinuousOn (fun time => referenceSize + dilation time + |stable time|) (Icc 0 finish) :=
    (continuousOn_const.add dilationContinuous).add stableContinuous.abs
  have dilationI := dilationContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have stableI := stableContinuous.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  refine ⟨fun time inside => ⟨momentEstimate time inside, dilationEstimate time inside⟩,
    coefficientContinuous, coefficientContinuous.intervalIntegrable_of_Icc finishNonnegative, stableI, ?_⟩
  rw [intervalIntegral.integral_add (intervalIntegrable_const.add dilationI) stableI,
    intervalIntegral.integral_add intervalIntegrable_const dilationI, intervalIntegral.integral_const]
  have comparison := mul_le_mul_of_nonneg_left dilationIntegralBound omegaNonnegative
  simpa only [smul_eq_mul, sub_zero] using (show omega * (finish * referenceSize +
      (∫ time in (0 : ℝ)..finish, dilation time) + ∫ time in (0 : ℝ)..finish, |stable time|) ≤
      omega * referenceSize * finish + omega * (∫ time in (0 : ℝ)..finish, |stable time|) +
        omega * forcingConstant * (1 / rate ^ 2 + 1 / rate ^ 3) * Real.exp (rate * (finish - origin)) by
    nlinarith only [comparison])

end EulerNonuniqueness.General

