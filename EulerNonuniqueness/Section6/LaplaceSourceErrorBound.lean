import EulerNonuniqueness.Section6.LaplaceMomentErrorBound

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

theorem laplace_source_error_bound {error first second : ℝ → ℂ}
    {decay constant firstCoefficient secondCoefficient horizon : ℝ}
    (errorMeasurable : Measurable error) (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (decayPositive : 0 < decay) (constantNonnegative : 0 ≤ constant)
    (firstNonnegative : 0 ≤ firstCoefficient) (secondNonnegative : 0 ≤ secondCoefficient)
    (horizonNonnegative : 0 ≤ horizon)
    (bound : ∀ time ∈ Icc 0 horizon,
      ‖error time‖ ≤ constant + firstCoefficient * ‖first time‖ + secondCoefficient * ‖second time‖) :
    IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖error time‖) volume 0 horizon ∧
      (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * ‖error time‖) ≤
        constant / decay + firstCoefficient * (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * ‖first time‖) +
          secondCoefficient * (∫ time in (0 : ℝ)..horizon, Real.exp (-decay * time) * ‖second time‖) := by
  let majorant := fun time => Real.exp (-decay * time) *
    (constant + firstCoefficient * ‖first time‖ + secondCoefficient * ‖second time‖)
  have majorantContinuous : Continuous majorant :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      ((continuous_const.add (continuous_const.mul firstContinuous.norm)).add
        (continuous_const.mul secondContinuous.norm))
  have pointwise (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖Real.exp (-decay * time) * ‖error time‖‖ ≤ majorant time := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left (bound time member) (Real.exp_pos _).le
  have majorantIntegrable : IntervalIntegrable majorant volume 0 horizon := majorantContinuous.intervalIntegrable _ _
  have integrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖error time‖) volume 0 horizon := majorantIntegrable.mono_fun'
    (((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul errorMeasurable.norm).aestronglyMeasurable.restrict)
    (by
      rw [uIoc_of_le horizonNonnegative]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time member
      exact pointwise time ⟨member.1.le, member.2⟩)
  refine ⟨integrable, ?_⟩
  have estimate := intervalIntegral.integral_mono_on horizonNonnegative integrable
    (majorantContinuous.intervalIntegrable 0 horizon) (fun time member => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))] using
        pointwise time member)
  have constantIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * constant) volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  have firstIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖first time‖) volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul firstContinuous.norm).intervalIntegrable _ _
  have secondIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * ‖second time‖) volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul secondContinuous.norm).intervalIntegrable _ _
  have expansion : majorant = fun time =>
      (Real.exp (-decay * time) * constant + firstCoefficient * (Real.exp (-decay * time) * ‖first time‖)) +
        secondCoefficient * (Real.exp (-decay * time) * ‖second time‖) := by
    funext time
    dsimp only [majorant]
    ring
  have sumIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * constant +
      firstCoefficient * (Real.exp (-decay * time) * ‖first time‖)) volume 0 horizon :=
    constantIntegrable.add (firstIntegrable.const_mul firstCoefficient)
  rw [expansion, intervalIntegral.integral_add sumIntegrable (secondIntegrable.const_mul secondCoefficient),
    intervalIntegral.integral_add constantIntegrable (firstIntegrable.const_mul firstCoefficient),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at estimate
  have constantBound := laplace_affine_integral_bound (slope := 0) decayPositive (by norm_num)
    constantNonnegative horizonNonnegative
  simp only [zero_mul, zero_add, zero_div] at constantBound
  linarith

end EulerNonuniqueness.Section6
