import EulerNonuniqueness.General.ExponentialAccumulatedAction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem accumulated_cost_le_of_exponential_majorants
    {dilationForcing forcing : ℝ → ℝ} {finish origin rate bound omega referenceSize : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (boundNonnegative : 0 ≤ bound) (omegaNonnegative : 0 ≤ omega)
    (dilationContinuous : ContinuousOn dilationForcing (Icc 0 finish))
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (dilationBound : ∀ time ∈ Icc 0 finish, dilationForcing time ≤ bound * Real.exp (rate * (time - origin)))
    (forcingBound : ∀ time ∈ Icc 0 finish, forcing time ≤ bound * Real.exp (rate * (time - origin))) :
    2 * omega * referenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationForcing time) +
        (∫ time in (0 : ℝ)..finish, forcing time) ≤
      2 * omega * referenceSize * finish +
        (2 * omega / rate ^ 2 + 1 / rate) * bound * Real.exp (rate * (finish - origin)) := by
  have dilationEstimate := (intervalIntegral.integral_sub_mul_le_of_exponential_majorant dilationContinuous
    finishNonnegative ratePositive boundNonnegative dilationBound).2
  have exponentialContinuous : Continuous (fun time : ℝ => bound * Real.exp (rate * (time - origin))) := by fun_prop
  have derivative (time : ℝ) : HasDerivAt
      (fun current => bound * Real.exp (rate * (current - origin)) / rate)
      (bound * Real.exp (rate * (time - origin))) time := by
    convert (((((hasDerivAt_id time).sub_const origin).const_mul rate).exp).const_mul bound).div_const rate using 1
    field_simp [ratePositive.ne']
    ring
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    (exponentialContinuous.intervalIntegrable 0 finish)
  have forcingEstimate := intervalIntegral.integral_mono_on finishNonnegative
    (forcingContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (exponentialContinuous.intervalIntegrable 0 finish) forcingBound
  rw [identity] at forcingEstimate
  have initialNonnegative : 0 ≤ bound * Real.exp (rate * (0 - origin)) / rate := by positivity
  have scaled := mul_le_mul_of_nonneg_left dilationEstimate (show 0 ≤ 2 * omega by positivity)
  calc
    _ ≤ 2 * omega * referenceSize * finish +
        2 * omega * (bound / rate ^ 2 * Real.exp (rate * (finish - origin))) +
        bound * Real.exp (rate * (finish - origin)) / rate := by
      linarith only [scaled, forcingEstimate, initialNonnegative]
    _ = _ := by ring

end EulerNonuniqueness.General
