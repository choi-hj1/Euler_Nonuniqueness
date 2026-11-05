import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem laplace_affine_integral_bound {decay slope constant horizon : ℝ}
    (decayPositive : 0 < decay) (slopeNonnegative : 0 ≤ slope) (constantNonnegative : 0 ≤ constant)
    (horizonNonnegative : 0 ≤ horizon) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * (slope * time + constant)) ≤
      slope / decay ^ 2 + constant / decay := by
  let primitive := fun time => -(Real.exp (-decay * time) *
    (slope * (decay * time + 1) + constant * decay)) / decay ^ 2
  have derivative (time : ℝ) : HasDerivAt primitive
      (Real.exp (-decay * time) * (slope * time + constant)) time := by
    have exponential := (((hasDerivAt_id time).const_mul (-decay)).exp)
    have linear := ((((hasDerivAt_id time).const_mul decay).add_const 1).const_mul slope).add_const (constant * decay)
    convert (exponential.mul linear).neg.div_const (decay ^ 2) using 1
    dsimp only
    field_simp [decayPositive.ne']
    <;> ring
  have integrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * (slope * time + constant))
      volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun time _ => derivative time) integrable
  have initial : primitive 0 = -(slope / decay ^ 2 + constant / decay) := by
    dsimp only [primitive]
    simp only [mul_zero, Real.exp_zero, zero_add, mul_one, one_mul]
    field_simp [decayPositive.ne']
    <;> ring
  have terminal : primitive horizon ≤ 0 := by
    dsimp only [primitive]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le
      (add_nonneg (mul_nonneg slopeNonnegative (by positivity)) (mul_nonneg constantNonnegative decayPositive.le))))
      (sq_nonneg decay)
  rw [initial] at identity
  linarith

theorem laplace_norm_error_integral_bound {error : ℝ → ℂ} {decay slope constant horizon : ℝ}
    (continuous : Continuous error) (decayPositive : 0 < decay)
    (slopeNonnegative : 0 ≤ slope) (constantNonnegative : 0 ≤ constant) (horizonNonnegative : 0 ≤ horizon)
    (bound : ∀ time ∈ Icc 0 horizon, ‖error time‖ ≤ slope * time + constant) :
    (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * ‖error time‖) ≤
      slope / decay ^ 2 + constant / decay := by
  have firstIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖error time‖) volume 0 horizon :=
    (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul continuous.norm)).intervalIntegrable _ _
  have secondIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * (slope * time + constant))
      volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  exact (intervalIntegral.integral_mono_on horizonNonnegative firstIntegrable secondIntegrable
    (fun time member => mul_le_mul_of_nonneg_left (bound time member) (Real.exp_pos _).le)).trans
      (laplace_affine_integral_bound decayPositive slopeNonnegative constantNonnegative horizonNonnegative)

end EulerNonuniqueness.Section6
