import EulerNonuniqueness.General.VariableHyperbolicBounds

open MeasureTheory Set

namespace EulerNonuniqueness

theorem scalar_variable_forward_bound
    {rate trajectory forcing : ℝ → ℝ} {decay horizon time : ℝ}
    (rateContinuous : Continuous rate)
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (rateUpper : ∀ current ∈ Icc 0 horizon, rate current ≤ -decay)
    (equation : ∀ current ∈ Icc 0 horizon,
      HasDerivAt trajectory (rate current * trajectory current + forcing current) current)
    (inside : time ∈ Icc 0 horizon) :
    |trajectory time| ≤ Real.exp (-decay * time) * |trajectory 0| +
      ∫ current in (0 : ℝ)..time, Real.exp (-decay * (time - current)) * |forcing current| := by
  have subset : uIcc 0 time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩
  have identity := scalar_variable_duhamel (first := 0) (last := time) rateContinuous
    (forcingContinuous.mono subset) (fun current membership => equation current (subset membership))
  have kernelBound (current : ℝ) (currentInside : current ∈ Icc 0 time) :
      Real.exp (ratePrimitive rate time - ratePrimitive rate current) ≤ Real.exp (-decay * (time - current)) := by
    apply Real.exp_le_exp.mpr
    have estimate := ratePrimitive_sub_upper rateContinuous currentInside.2
      (fun position membership => rateUpper position ⟨currentInside.1.trans membership.1, membership.2.trans inside.2⟩)
    linarith
  have kernelContinuous : Continuous (fun current : ℝ =>
      Real.exp (ratePrimitive rate time - ratePrimitive rate current)) :=
    Real.continuous_exp.comp (continuous_const.sub (ratePrimitive_continuous rateContinuous))
  have forcingOn : ContinuousOn forcing (Icc 0 time) :=
    forcingContinuous.mono (fun _ membership => ⟨membership.1, membership.2.trans inside.2⟩)
  have integrable : IntervalIntegrable (fun current =>
      Real.exp (ratePrimitive rate time - ratePrimitive rate current) * |forcing current|) volume 0 time :=
    (kernelContinuous.continuousOn.mul forcingOn.abs).intervalIntegrable_of_Icc inside.1
  have majorantIntegrable : IntervalIntegrable (fun current =>
      Real.exp (-decay * (time - current)) * |forcing current|) volume 0 time :=
    ((by fun_prop : Continuous (fun current : ℝ => Real.exp (-decay * (time - current)))).continuousOn.mul
      forcingOn.abs).intervalIntegrable_of_Icc inside.1
  rw [identity]
  calc
    _ ≤ |Real.exp (ratePrimitive rate time - ratePrimitive rate 0) * trajectory 0| +
        |∫ current in (0 : ℝ)..time, Real.exp (ratePrimitive rate time - ratePrimitive rate current) * forcing current| :=
      abs_add _ _
    _ ≤ Real.exp (-decay * time) * |trajectory 0| +
        ∫ current in (0 : ℝ)..time, Real.exp (ratePrimitive rate time - ratePrimitive rate current) * |forcing current| := by
      apply add_le_add
      · rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        simpa only [sub_zero] using mul_le_mul_of_nonneg_right
          (kernelBound 0 ⟨le_rfl, inside.1⟩) (abs_nonneg (trajectory 0))
      · have estimate := intervalIntegral.norm_integral_le_integral_norm
          (μ := volume)
          (f := fun current => Real.exp (ratePrimitive rate time - ratePrimitive rate current) * forcing current) inside.1
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using estimate
    _ ≤ _ := add_le_add_left
      (intervalIntegral.integral_mono_on inside.1 integrable majorantIntegrable
        (fun current membership => mul_le_mul_of_nonneg_right (kernelBound current membership) (abs_nonneg _))) _

end EulerNonuniqueness
