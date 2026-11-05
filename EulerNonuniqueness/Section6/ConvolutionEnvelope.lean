import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem exponential_convolution_envelope {forcing : ℝ → ℝ}
    {growth decay amplitude horizon time : ℝ}
    (continuous : ContinuousOn forcing (Icc 0 horizon))
    (differentRates : decay < growth) (amplitudeNonnegative : 0 ≤ amplitude)
    (bounded : ∀ current ∈ Icc 0 horizon, forcing current ≤ amplitude * Real.exp (growth * current))
    (inside : time ∈ Icc 0 horizon) :
    (∫ current in (0 : ℝ)..time, Real.exp (decay * (time - current)) * forcing current) ≤
      amplitude * Real.exp (growth * time) / (growth - decay) := by
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have kernelContinuous : ContinuousOn (fun current => Real.exp (decay * (time - current))) (uIcc 0 time) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have sourceContinuous : ContinuousOn (fun current => amplitude * Real.exp (growth * current)) (uIcc 0 time) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  apply le_trans _ (exponential_convolution_le differentRates amplitudeNonnegative)
  apply intervalIntegral.integral_mono_on inside.1
    (kernelContinuous.mul (continuous.mono intervalInside)).intervalIntegrable
    (kernelContinuous.mul sourceContinuous).intervalIntegrable
  intro current currentInside
  exact mul_le_mul_of_nonneg_left (bounded current ⟨currentInside.1, currentInside.2.trans inside.2⟩) (Real.exp_pos _).le

end EulerNonuniqueness.Section6
