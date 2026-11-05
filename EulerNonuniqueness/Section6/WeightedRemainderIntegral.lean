import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem weighted_remainder_integral_bound {remainder : ℝ → ℝ}
    {growth slowRate scale constant fastAmplitude slowAmplitude horizon : ℝ}
    (growthPositive : 0 < growth) (slowPositive : 0 < slowRate)
    (scaleNonnegative : 0 ≤ scale) (constantNonnegative : 0 ≤ constant)
    (fastNonnegative : 0 ≤ fastAmplitude) (slowNonnegative : 0 ≤ slowAmplitude)
    (horizonNonnegative : 0 ≤ horizon)
    (measurable : AEStronglyMeasurable remainder (volume.restrict (Icc 0 horizon)))
    (bounded : ∀ time ∈ Icc 0 horizon, |remainder time| ≤ scale * Real.exp (growth * time) *
      (constant + fastAmplitude * Real.exp (growth * time) + slowAmplitude * Real.exp (slowRate * time))) :
    IntervalIntegrable (fun time => Real.exp (-growth * time) * remainder time) volume 0 horizon ∧
      ∀ time ∈ Icc 0 horizon,
        |∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * remainder current| ≤
          scale * (constant * time + fastAmplitude * Real.exp (growth * time) / growth +
            slowAmplitude * Real.exp (slowRate * time) / slowRate) := by
  let majorant := fun time => scale * (constant + fastAmplitude * Real.exp (growth * time) +
    slowAmplitude * Real.exp (slowRate * time))
  have majorantContinuous : Continuous majorant := by dsimp only [majorant]; fun_prop
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      |Real.exp (-growth * time) * remainder time| ≤ majorant time := by
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have estimate := mul_le_mul_of_nonneg_left (bounded time inside) (Real.exp_pos (-growth * time)).le
    have cancellation : Real.exp (-growth * time) * Real.exp (growth * time) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      _ ≤ _ := estimate
      _ = scale * (Real.exp (-growth * time) * Real.exp (growth * time)) *
          (constant + fastAmplitude * Real.exp (growth * time) + slowAmplitude * Real.exp (slowRate * time)) := by ring
      _ = _ := by dsimp only [majorant]; rw [cancellation, mul_one]
  have weightedIntegrable : IntegrableOn (fun time => Real.exp (-growth * time) * remainder time) (Icc 0 horizon) := by
    apply majorantContinuous.continuousOn.integrableOn_Icc.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mul measurable)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with time inside
    simpa only [Real.norm_eq_abs] using pointwise time inside
  have intervalIntegrable := (intervalIntegrable_iff_integrableOn_Icc_of_le horizonNonnegative).mpr weightedIntegrable
  refine ⟨intervalIntegrable, ?_⟩
  intro time inside
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have localIntegrable := intervalIntegrable.mono_set (intervalInside.trans Icc_subset_uIcc)
  have integralBound : |∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * remainder current| ≤
      ∫ current in (0 : ℝ)..time, majorant current := by
    apply (intervalIntegral.abs_integral_le_integral_abs inside.1).trans
    apply intervalIntegral.integral_mono_on inside.1 localIntegrable.abs (majorantContinuous.intervalIntegrable 0 time)
    intro current currentInside
    exact pointwise current ⟨currentInside.1, currentInside.2.trans inside.2⟩
  have exponentialIntegrable (rate : ℝ) : IntervalIntegrable (fun current => Real.exp (rate * current)) volume 0 time :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
  have majorantIntegral : (∫ current in (0 : ℝ)..time, majorant current) =
      scale * (constant * time + fastAmplitude * ((Real.exp (growth * time) - 1) / growth) +
        slowAmplitude * ((Real.exp (slowRate * time) - 1) / slowRate)) := by
    dsimp only [majorant]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (intervalIntegrable_const.add ((exponentialIntegrable growth).const_mul fastAmplitude))
        ((exponentialIntegrable slowRate).const_mul slowAmplitude),
      intervalIntegral.integral_add intervalIntegrable_const ((exponentialIntegrable growth).const_mul fastAmplitude),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_exp_mul_real growthPositive.ne', integral_exp_mul_real slowPositive.ne']
    simp only [mul_zero, Real.exp_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  apply integralBound.trans
  rw [majorantIntegral]
  apply mul_le_mul_of_nonneg_left _ scaleNonnegative
  have fastBound := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_self (Real.exp (growth * time)) zero_le_one) growthPositive.le) fastNonnegative
  have slowBound := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right (sub_le_self (Real.exp (slowRate * time)) zero_le_one) slowPositive.le) slowNonnegative
  convert add_le_add (add_le_add_left fastBound (constant * time)) slowBound using 1 <;> ring

end EulerNonuniqueness.Section6
