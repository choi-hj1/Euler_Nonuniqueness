import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem integral_sub_mul_le_of_exponential_majorant
    {function : ℝ → ℝ} {finish origin rate bound : ℝ}
    (regular : ContinuousOn function (Icc 0 finish))
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate) (boundNonnegative : 0 ≤ bound)
    (majorized : ∀ time ∈ Icc 0 finish, function time ≤ bound * Real.exp (rate * (time - origin))) :
    IntervalIntegrable (fun time => (finish - time) * function time) volume 0 finish ∧
      (∫ time in (0 : ℝ)..finish, (finish - time) * function time) ≤
        bound / rate ^ 2 * Real.exp (rate * (finish - origin)) := by
  let primitive := fun time => bound * Real.exp (rate * (time - origin)) *
    ((finish - time) / rate + 1 / rate ^ 2)
  have derivative (time : ℝ) : HasDerivAt primitive
      ((finish - time) * (bound * Real.exp (rate * (time - origin)))) time := by
    have exponential := ((((hasDerivAt_id time).sub_const origin).const_mul rate).exp).const_mul bound
    have affine := (((hasDerivAt_id time).const_sub finish).div_const rate).add_const (1 / rate ^ 2)
    convert exponential.mul affine using 1
    field_simp [ratePositive.ne']
    ring
  have integrable : ContinuousOn (fun time => (finish - time) * function time) (Icc 0 finish) :=
    (continuousOn_const.sub continuousOn_id).mul regular
  have exponentialRegular : Continuous (fun time : ℝ =>
      (finish - time) * (bound * Real.exp (rate * (time - origin)))) := by fun_prop
  have identity := integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    (exponentialRegular.intervalIntegrable 0 finish)
  have initialNonnegative : 0 ≤ primitive 0 := by
    dsimp only [primitive]
    simp only [sub_zero]
    positivity
  have terminal : primitive finish = bound / rate ^ 2 * Real.exp (rate * (finish - origin)) := by
    dsimp only [primitive]
    simp only [sub_self, zero_div, zero_add]
    ring
  have comparison := integral_mono_on finishNonnegative
    (integrable.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (exponentialRegular.intervalIntegrable 0 finish) (fun time inside =>
      mul_le_mul_of_nonneg_left (majorized time inside) (sub_nonneg.mpr inside.2))
  rw [identity, terminal] at comparison
  exact ⟨integrable.intervalIntegrable_of_Icc finishNonnegative, by linarith only [comparison, initialNonnegative]⟩

end intervalIntegral

namespace EulerNonuniqueness.General

theorem accumulated_coefficient_action_le_of_exponential_majorants
    {coefficient dilationForcing forcing : ℝ → ℝ} {finish origin rate bound omega referenceSize : ℝ}
    (finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate)
    (boundNonnegative : 0 ≤ bound) (omegaNonnegative : 0 ≤ omega)
    (dilationContinuous : ContinuousOn dilationForcing (Icc 0 finish))
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (action : omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
      2 * omega * referenceSize * finish +
        2 * omega * (∫ time in (0 : ℝ)..finish, (finish - time) * dilationForcing time) +
        ∫ time in (0 : ℝ)..finish, forcing time)
    (dilationBound : ∀ time ∈ Icc 0 finish, dilationForcing time ≤ bound * Real.exp (rate * (time - origin)))
    (forcingBound : ∀ time ∈ Icc 0 finish, forcing time ≤ bound * Real.exp (rate * (time - origin))) :
    omega * (∫ time in (0 : ℝ)..finish, coefficient time) ≤
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
      linarith only [action, scaled, forcingEstimate, initialNonnegative]
    _ = _ := by ring

end EulerNonuniqueness.General
