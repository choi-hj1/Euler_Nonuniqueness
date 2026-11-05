import EulerNonuniqueness.General.VariableLinearDuhamel

open MeasureTheory Set

namespace EulerNonuniqueness

noncomputable section

theorem ratePrimitive_sub_eq_integral {rate : ℝ → ℝ} (rateContinuous : Continuous rate)
    (first last : ℝ) :
    ratePrimitive rate last - ratePrimitive rate first = ∫ time in first..last, rate time := by
  have identity := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (rateContinuous.intervalIntegrable 0 first) (rateContinuous.intervalIntegrable first last)
  change ratePrimitive rate first + (∫ time in first..last, rate time) = ratePrimitive rate last at identity
  linarith

theorem ratePrimitive_sub_lower {rate : ℝ → ℝ} {lower first last : ℝ}
    (rateContinuous : Continuous rate) (ordered : first ≤ last)
    (rateLower : ∀ time ∈ Icc first last, lower ≤ rate time) :
    lower * (last - first) ≤ ratePrimitive rate last - ratePrimitive rate first := by
  rw [ratePrimitive_sub_eq_integral rateContinuous]
  have estimate := intervalIntegral.integral_mono_on ordered
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => lower) volume first last)
    (rateContinuous.intervalIntegrable first last) rateLower
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using estimate

theorem ratePrimitive_sub_upper {rate : ℝ → ℝ} {upper first last : ℝ}
    (rateContinuous : Continuous rate) (ordered : first ≤ last)
    (rateUpper : ∀ time ∈ Icc first last, rate time ≤ upper) :
    ratePrimitive rate last - ratePrimitive rate first ≤ upper * (last - first) := by
  rw [ratePrimitive_sub_eq_integral rateContinuous]
  have estimate := intervalIntegral.integral_mono_on ordered
    (rateContinuous.intervalIntegrable first last)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => upper) volume first last) rateUpper
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using estimate

theorem scalar_variable_backward_bound
    {rate trajectory forcing : ℝ → ℝ} {decay horizon time : ℝ}
    (rateContinuous : Continuous rate)
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (rateLower : ∀ current ∈ Icc 0 horizon, decay ≤ rate current)
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory (rate current * trajectory current + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    |trajectory time| ≤ Real.exp (-decay * (horizon - time)) * |trajectory horizon| +
      ∫ current in time..horizon, Real.exp (-decay * (current - time)) * |forcing current| := by
  have subset : uIcc horizon time ⊆ Icc 0 horizon := by
    rw [uIcc_comm, uIcc_of_le inside.2]
    exact fun _ membership => ⟨inside.1.trans membership.1, membership.2⟩
  have identity := scalar_variable_duhamel (first := horizon) (last := time) rateContinuous
    (forcingContinuous.mono subset) (fun current membership => equation current (subset membership))
  rw [intervalIntegral.integral_symm] at identity
  have kernelBound (current : ℝ) (currentInside : current ∈ Icc time horizon) :
      Real.exp (ratePrimitive rate time - ratePrimitive rate current) ≤ Real.exp (-decay * (current - time)) := by
    apply Real.exp_le_exp.mpr
    have estimate := ratePrimitive_sub_lower rateContinuous currentInside.1
      (fun position membership => rateLower position ⟨inside.1.trans membership.1, membership.2.trans currentInside.2⟩)
    linarith
  have kernelContinuous : Continuous (fun current : ℝ =>
      Real.exp (ratePrimitive rate time - ratePrimitive rate current)) :=
    Real.continuous_exp.comp (continuous_const.sub (ratePrimitive_continuous rateContinuous))
  have forcingOn : ContinuousOn forcing (Icc time horizon) :=
    forcingContinuous.mono (fun _ membership => ⟨inside.1.trans membership.1, membership.2⟩)
  have integrable : IntervalIntegrable (fun current =>
      Real.exp (ratePrimitive rate time - ratePrimitive rate current) * |forcing current|) volume time horizon :=
    (kernelContinuous.continuousOn.mul forcingOn.abs).intervalIntegrable_of_Icc inside.2
  have majorantIntegrable : IntervalIntegrable (fun current =>
      Real.exp (-decay * (current - time)) * |forcing current|) volume time horizon :=
    ((by fun_prop : Continuous (fun current : ℝ => Real.exp (-decay * (current - time)))).continuousOn.mul
      forcingOn.abs).intervalIntegrable_of_Icc inside.2
  rw [identity]
  calc
    _ ≤ |Real.exp (ratePrimitive rate time - ratePrimitive rate horizon) * trajectory horizon| +
        |∫ current in time..horizon, Real.exp (ratePrimitive rate time - ratePrimitive rate current) * forcing current| :=
      abs_sub _ _
    _ ≤ Real.exp (-decay * (horizon - time)) * |trajectory horizon| +
        ∫ current in time..horizon, Real.exp (ratePrimitive rate time - ratePrimitive rate current) * |forcing current| := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (kernelBound horizon ⟨inside.2, le_rfl⟩) (abs_nonneg _)
      · have estimate := intervalIntegral.norm_integral_le_integral_norm
          (μ := volume)
          (f := fun current => Real.exp (ratePrimitive rate time - ratePrimitive rate current) * forcing current) inside.2
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using estimate
    _ ≤ _ := add_le_add_left
      (intervalIntegral.integral_mono_on inside.2 integrable majorantIntegrable
        (fun current membership => mul_le_mul_of_nonneg_right (kernelBound current membership) (abs_nonneg _))) _

end

end EulerNonuniqueness
