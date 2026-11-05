import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem weighted_integral_le_of_history_majorant
    {history forcing : ℝ → ℝ} {horizon weight : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (weightPositive : 0 < weight)
    (historyContinuous : ContinuousOn history (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (historyBound : ∀ time ∈ Icc 0 horizon,
      history time ≤ ∫ current in (0 : ℝ)..time, forcing current) :
    weight * (∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * history time) ≤
      ∫ time in (0 : ℝ)..horizon, Real.exp (-weight * time) * forcing time := by
  have forcingIntegrable := forcingContinuous.intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  have primitiveContinuous : ContinuousOn (fun time => ∫ current in (0 : ℝ)..time, forcing current) (Icc 0 horizon) := by
    simpa only [uIcc_of_le horizonNonnegative] using
      intervalIntegral.continuousOn_primitive_interval' forcingIntegrable left_mem_uIcc
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have comparison := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    ((weightContinuous.continuousOn.mul historyContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative)
    ((weightContinuous.continuousOn.mul primitiveContinuous).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (historyBound time inside) (Real.exp_pos _).le)
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le
    (rate := (0 : ℝ)) forcingContinuous weightPositive horizonNonnegative forcingNonnegative
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero] at convolution
  simpa only [mul_comm] using (le_div_iff₀ weightPositive).mp (comparison.trans convolution)

end EulerNonuniqueness.General
