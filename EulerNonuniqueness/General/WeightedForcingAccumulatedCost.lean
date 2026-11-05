import EulerNonuniqueness.General.ExponentialPowerTail
import EulerNonuniqueness.General.ExponentialAccumulatedAction
import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem integral_terminal_moment_le_weighted
    {forcing : ℝ → ℝ} {finish rate : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (regular : ContinuousOn forcing (Icc 0 finish))
    (nonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ forcing time) :
    (∫ time in (0 : ℝ)..finish, (finish - time) * forcing time) ≤
      Real.exp (rate * finish) / rate *
        (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * forcing time) := by
  have weightedContinuous : ContinuousOn (fun time => Real.exp (-rate * time) * forcing time) (Icc 0 finish) :=
    (by fun_prop : Continuous (fun time : ℝ => Real.exp (-rate * time))).continuousOn.mul regular
  rw [← integral_const_mul]
  apply integral_mono_on finishNonnegative
    (((continuousOn_const.sub continuousOn_id).mul regular).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    ((weightedContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative).const_mul _)
  intro time inside
  have polynomial := EulerNonuniqueness.pow_mul_exp_neg_mul_le_factorial 1 ratePositive
    (sub_nonneg.mpr inside.2)
  simp only [pow_one, Nat.factorial_one, Nat.cast_one] at polynomial
  have multiplied := mul_le_mul_of_nonneg_right polynomial (Real.exp_pos (rate * (finish - time))).le
  have cancellation : Real.exp (-rate * (finish - time)) * Real.exp (rate * (finish - time)) = 1 := by
    rw [← Real.exp_add, show -rate * (finish - time) + rate * (finish - time) = 0 by ring, Real.exp_zero]
  rw [mul_assoc, cancellation, mul_one] at multiplied
  have exponentIdentity : Real.exp (rate * finish) / rate * Real.exp (-rate * time) =
      1 / rate * Real.exp (rate * (finish - time)) := by
    calc
      _ = rate⁻¹ * (Real.exp (rate * finish) * Real.exp (-rate * time)) := by ring
      _ = rate⁻¹ * Real.exp (rate * (finish - time)) := by
        rw [← Real.exp_add]
        congr 2
        ring
      _ = _ := by ring
  rw [← mul_assoc, exponentIdentity]
  exact mul_le_mul_of_nonneg_right multiplied (nonnegative time inside)

end intervalIntegral

namespace EulerNonuniqueness.General

theorem accumulated_cost_le_of_state_profile_and_weighted_forcing
    {state foreign dilationForcing forcing : ℝ → ℝ}
    {finish origin rate omega constant stateBound foreignBound referenceSize : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (omegaNonnegative : 0 ≤ omega) (omegaRate : omega ≤ rate)
    (constantNonnegative : 0 ≤ constant) (stateNonnegative : 0 ≤ stateBound)
    (foreignBoundNonnegative : 0 ≤ foreignBound)
    (stateContinuous : ContinuousOn state (Icc 0 finish))
    (foreignContinuous : ContinuousOn foreign (Icc 0 finish))
    (dilationContinuous : ContinuousOn dilationForcing (Icc 0 finish))
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (foreignNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ foreign time)
    (profile : ∀ time ∈ Icc 0 finish, state time ≤ stateBound * Real.exp (rate * (time - origin)))
    (weightedForcing : (∫ time in (0 : ℝ)..finish, Real.exp (-rate * time) * foreign time) ≤
      foreignBound * Real.exp (-rate * origin))
    (dilationBound : ∀ time ∈ Icc 0 finish,
      dilationForcing time ≤ constant * (omega * state time + foreign time))
    (forcingBound : ∀ time ∈ Icc 0 finish,
      forcing time ≤ constant * (omega * state time + foreign time)) :
    2 * omega * referenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationForcing time) +
        (∫ time in (0 : ℝ)..finish, forcing time) ≤
      2 * omega * referenceSize * finish +
        3 * constant * (stateBound + foreignBound) * Real.exp (rate * (finish - origin)) := by
  have stateI := stateContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have foreignI := foreignContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have stateMomentI : IntervalIntegrable (fun time : ℝ => (finish - time) * state time) volume 0 finish :=
    ((continuousOn_const.sub continuousOn_id).mul stateContinuous).intervalIntegrable_of_Icc finishNonnegative
  have foreignMomentI : IntervalIntegrable (fun time : ℝ => (finish - time) * foreign time) volume 0 finish :=
    ((continuousOn_const.sub continuousOn_id).mul foreignContinuous).intervalIntegrable_of_Icc finishNonnegative
  have weightedI := ((by fun_prop : Continuous (fun time : ℝ => Real.exp (-rate * time))).continuousOn.mul
    foreignContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have stateEstimate := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant
    (firstRate := 0) finishNonnegative ratePositive stateNonnegative
    (by simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using stateI) profile
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, sub_zero] at stateEstimate
  have stateMoment := (intervalIntegral.integral_sub_mul_le_of_exponential_majorant
    stateContinuous finishNonnegative ratePositive stateNonnegative profile).2
  have foreignEstimate := intervalIntegral.exp_mul_integral_weighted_mono_rate
    (firstRate := 0) finishNonnegative ratePositive.le
    (by simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul] using foreignI) weightedI foreignNonnegative
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at foreignEstimate
  have foreignMoment := intervalIntegral.integral_terminal_moment_le_weighted
    finishNonnegative ratePositive foreignContinuous foreignNonnegative
  have rateRatioNonnegative : 0 ≤ omega / rate := div_nonneg omegaNonnegative ratePositive.le
  have rateRatioOne : omega / rate ≤ 1 := (div_le_one ratePositive).mpr omegaRate
  have squareRatioOne : omega ^ 2 / rate ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos ratePositive)).mpr
    (pow_le_pow_left₀ omegaNonnegative omegaRate 2)
  have exponentialNonnegative : 0 ≤ Real.exp (rate * (finish - origin)) := (Real.exp_pos _).le
  have stateScaled : omega * (∫ time in (0 : ℝ)..finish, state time) ≤
      stateBound * Real.exp (rate * (finish - origin)) := by
    apply (mul_le_mul_of_nonneg_left stateEstimate omegaNonnegative).trans
    convert mul_le_mul_of_nonneg_right rateRatioOne (mul_nonneg stateNonnegative exponentialNonnegative) using 1 <;> ring
  have stateMomentScaled : omega ^ 2 * (∫ time in (0 : ℝ)..finish, (finish - time) * state time) ≤
      stateBound * Real.exp (rate * (finish - origin)) := by
    apply (mul_le_mul_of_nonneg_left stateMoment (sq_nonneg omega)).trans
    convert mul_le_mul_of_nonneg_right squareRatioOne (mul_nonneg stateNonnegative exponentialNonnegative) using 1 <;> ring
  have exponentialIdentity : Real.exp (rate * finish) * Real.exp (-rate * origin) =
      Real.exp (rate * (finish - origin)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have foreignScaled : (∫ time in (0 : ℝ)..finish, foreign time) ≤
      foreignBound * Real.exp (rate * (finish - origin)) := by
    apply foreignEstimate.trans
    apply (mul_le_mul_of_nonneg_left weightedForcing (Real.exp_pos _).le).trans_eq
    rw [mul_left_comm, exponentialIdentity]
  have foreignMomentScaled : omega * (∫ time in (0 : ℝ)..finish, (finish - time) * foreign time) ≤
      foreignBound * Real.exp (rate * (finish - origin)) := by
    have weightedScaled := mul_le_mul_of_nonneg_left weightedForcing
      (show 0 ≤ Real.exp (rate * finish) / rate by positivity)
    have intermediate := mul_le_mul_of_nonneg_left (foreignMoment.trans weightedScaled) omegaNonnegative
    apply intermediate.trans
    convert mul_le_mul_of_nonneg_right rateRatioOne (mul_nonneg foreignBoundNonnegative exponentialNonnegative) using 1
    · rw [← exponentialIdentity]; ring
    · ring
  have upperContinuous : ContinuousOn (fun time => constant * (omega * state time + foreign time)) (Icc 0 finish) :=
    continuousOn_const.mul ((continuousOn_const.mul stateContinuous).add foreignContinuous)
  have forcingIntegral := intervalIntegral.integral_mono_on finishNonnegative
    (forcingContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (upperContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative) forcingBound
  have dilationIntegral := intervalIntegral.integral_mono_on finishNonnegative
    (((continuousOn_const.sub continuousOn_id).mul dilationContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (((continuousOn_const.sub continuousOn_id).mul upperContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (dilationBound time inside) (sub_nonneg.mpr inside.2))
  have expandedForcing : (∫ time in (0 : ℝ)..finish, constant * (omega * state time + foreign time)) =
      constant * (omega * (∫ time in (0 : ℝ)..finish, state time) + ∫ time in (0 : ℝ)..finish, foreign time) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (stateI.const_mul omega) foreignI,
      intervalIntegral.integral_const_mul]
  have expandedDilation : (∫ time in (0 : ℝ)..finish, (finish - time) * (constant * (omega * state time + foreign time))) =
      constant * (omega * (∫ time in (0 : ℝ)..finish, (finish - time) * state time) +
        ∫ time in (0 : ℝ)..finish, (finish - time) * foreign time) := by
    simp_rw [show ∀ time, (finish - time) * (constant * (omega * state time + foreign time)) =
      constant * (omega * ((finish - time) * state time) + (finish - time) * foreign time) by intro time; ring]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
      (stateMomentI.const_mul omega) foreignMomentI,
      intervalIntegral.integral_const_mul]
  rw [expandedForcing] at forcingIntegral
  change (∫ time in (0 : ℝ)..finish, (finish - time) * dilationForcing time) ≤
    ∫ time in (0 : ℝ)..finish, (finish - time) * (constant * (omega * state time + foreign time)) at dilationIntegral
  rw [expandedDilation] at dilationIntegral
  have forcingFinal := forcingIntegral.trans (mul_le_mul_of_nonneg_left (add_le_add stateScaled foreignScaled) constantNonnegative)
  have dilationScaled := mul_le_mul_of_nonneg_left dilationIntegral omegaNonnegative
  have dilationFinal : omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationForcing time) ≤
      constant * ((stateBound + foreignBound) * Real.exp (rate * (finish - origin))) := by
    apply dilationScaled.trans
    convert mul_le_mul_of_nonneg_left (add_le_add stateMomentScaled foreignMomentScaled) constantNonnegative using 1 <;> ring
  nlinarith only [forcingFinal, dilationFinal]

end EulerNonuniqueness.General
