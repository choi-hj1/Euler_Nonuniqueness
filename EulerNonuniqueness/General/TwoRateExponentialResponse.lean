import Mathlib.Analysis.SpecialFunctions.Integrals

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem exp_mul_integral_weighted_mono_rate
    {forcing : ℝ → ℝ} {finish firstRate secondRate : ℝ}
    (finishNonnegative : 0 ≤ finish) (ordered : firstRate ≤ secondRate)
    (firstIntegrable : IntervalIntegrable (fun time => Real.exp (-firstRate * time) * forcing time) volume 0 finish)
    (secondIntegrable : IntervalIntegrable (fun time => Real.exp (-secondRate * time) * forcing time) volume 0 finish)
    (nonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ forcing time) :
    Real.exp (firstRate * finish) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-firstRate * time) * forcing time) ≤
      Real.exp (secondRate * finish) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-secondRate * time) * forcing time) := by
  have exponentialIdentity (rate time : ℝ) :
      Real.exp (rate * finish) * (Real.exp (-rate * time) * forcing time) =
        Real.exp (rate * (finish - time)) * forcing time := by
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_mono_on finishNonnegative
  · exact firstIntegrable.const_mul _
  · exact secondIntegrable.const_mul _
  · intro time inside
    rw [exponentialIdentity, exponentialIdentity]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right ordered (sub_nonneg.mpr inside.2))) (nonnegative time inside)

theorem exp_mul_integral_le_of_faster_exponential_majorant
    {function : ℝ → ℝ} {finish origin firstRate secondRate bound : ℝ}
    (finishNonnegative : 0 ≤ finish) (ordered : firstRate < secondRate)
    (boundNonnegative : 0 ≤ bound)
    (integrable : IntervalIntegrable (fun time => Real.exp (-firstRate * time) * function time) volume 0 finish)
    (majorized : ∀ time ∈ Icc 0 finish,
      function time ≤ bound * Real.exp (secondRate * (time - origin))) :
    Real.exp (firstRate * finish) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-firstRate * time) * function time) ≤
      bound / (secondRate - firstRate) * Real.exp (secondRate * (finish - origin)) := by
  let upper := fun time => Real.exp (-firstRate * time) *
    (bound * Real.exp (secondRate * (time - origin)))
  let primitive := fun time => bound / (secondRate - firstRate) *
    Real.exp (-firstRate * time + secondRate * (time - origin))
  have gapPositive : 0 < secondRate - firstRate := sub_pos.mpr ordered
  have derivative (time : ℝ) : HasDerivAt primitive (upper time) time := by
    have exponent := ((hasDerivAt_id time).const_mul (-firstRate)).add
      (((hasDerivAt_id time).sub_const origin).const_mul secondRate)
    convert exponent.exp.const_mul (bound / (secondRate - firstRate)) using 1
    dsimp only [upper]
    rw [Real.exp_add]
    field_simp
    ring
  have upperContinuous : Continuous upper := by dsimp only [upper]; fun_prop
  have identity := integral_eq_sub_of_hasDerivAt (fun time _ => derivative time)
    (upperContinuous.intervalIntegrable 0 finish)
  have comparison := integral_mono_on finishNonnegative
    integrable
    (upperContinuous.intervalIntegrable 0 finish)
    (fun time inside => mul_le_mul_of_nonneg_left (majorized time inside) (Real.exp_pos _).le)
  change (∫ time in (0 : ℝ)..finish, Real.exp (-firstRate * time) * function time) ≤
    ∫ time in (0 : ℝ)..finish, upper time at comparison
  rw [identity] at comparison
  have initialNonnegative : 0 ≤ primitive 0 := by dsimp only [primitive]; positivity
  have integrated := mul_le_mul_of_nonneg_left
    (comparison.trans (sub_le_self _ initialNonnegative)) (Real.exp_pos (firstRate * finish)).le
  apply integrated.trans_eq
  dsimp only [primitive]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end intervalIntegral

namespace EulerNonuniqueness.General

theorem two_rate_exponential_response_le
    {shape forcing : ℝ → ℝ} {finish origin firstRate secondRate bound : ℝ}
    (finishNonnegative : 0 ≤ finish) (firstNonnegative : 0 ≤ firstRate)
    (ordered : firstRate < secondRate) (boundNonnegative : 0 ≤ bound)
    (shapeIntegrable : IntervalIntegrable (fun time => Real.exp (-firstRate * time) * shape time) volume 0 finish)
    (forcingFirstIntegrable : IntervalIntegrable (fun time => Real.exp (-firstRate * time) * forcing time) volume 0 finish)
    (forcingSecondIntegrable : IntervalIntegrable (fun time => Real.exp (-secondRate * time) * forcing time) volume 0 finish)
    (forcingNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ forcing time)
    (majorized : ∀ time ∈ Icc 0 finish,
      shape time ≤ bound * Real.exp (secondRate * (time - origin))) :
    Real.exp (firstRate * finish) *
        (firstRate * (∫ time in (0 : ℝ)..finish, Real.exp (-firstRate * time) * shape time) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-firstRate * time) * forcing time) ≤
      firstRate / (secondRate - firstRate) * bound * Real.exp (secondRate * (finish - origin)) +
        Real.exp (secondRate * finish) *
          (∫ time in (0 : ℝ)..finish, Real.exp (-secondRate * time) * forcing time) := by
  have shapeBound := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant
    finishNonnegative ordered boundNonnegative shapeIntegrable majorized
  have forcingBound := intervalIntegral.exp_mul_integral_weighted_mono_rate
    finishNonnegative ordered.le forcingFirstIntegrable forcingSecondIntegrable forcingNonnegative
  have combined := add_le_add (mul_le_mul_of_nonneg_left shapeBound firstNonnegative) forcingBound
  convert combined using 1 <;> ring

end EulerNonuniqueness.General
