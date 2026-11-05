import EulerNonuniqueness.General.WeightedResponseIntegral
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem stable_integral_of_original_history
    {relative leading remainder : ℝ → ℝ × ℝ} {growth finish : ℝ}
    (growthPositive : 0 < growth) (finishNonnegative : 0 ≤ finish)
    (relativeContinuous : ContinuousOn relative (Icc 0 finish))
    (leadingContinuous : ContinuousOn leading (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (identity : ∀ time ∈ Icc 0 finish, (relative time).2 =
      ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * (leading current + remainder current).2) :
    growth * (∫ time in (0 : ℝ)..finish, |(relative time).2|) ≤
      (∫ time in (0 : ℝ)..finish, |(leading time).2|) + ∫ time in (0 : ℝ)..finish, ‖remainder time‖ := by
  let forcing := fun time => |(leading time).2| + ‖remainder time‖
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) := leadingContinuous.snd.abs.add remainderContinuous.norm
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := add_nonneg (abs_nonneg _) (norm_nonneg _)
  let extended := fun time => forcing (projIcc 0 finish finishNonnegative time)
  have extendedContinuous : Continuous extended :=
    continuousOn_iff_continuous_restrict.mp forcingContinuous |>.comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 finish) : extended time = forcing time := by
    simp only [extended, projIcc_of_mem finishNonnegative inside]
  let kernel := fun time => ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * forcing current
  have kernelAgreement (time : ℝ) (inside : time ∈ Icc 0 finish) :
      EulerNonuniqueness.exponentialResponse (-growth) extended time = kernel time := by
    rw [EulerNonuniqueness.exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (-growth * (time - current)) * extended current = _
    rw [agreement current ⟨member.1, member.2.trans inside.2⟩]
  have responseContinuous : Continuous (EulerNonuniqueness.exponentialResponse (-growth) extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (EulerNonuniqueness.hasDerivAt_exponentialResponse extendedContinuous (-growth) time).continuousAt
  have kernelContinuous : ContinuousOn kernel (Icc 0 finish) :=
    responseContinuous.continuousOn.congr (fun time inside => (kernelAgreement time inside).symm)
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : |(relative time).2| ≤ kernel time := by
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have exponential : Continuous (fun current : ℝ => Real.exp (-growth * (time - current))) := by fun_prop
    have absoluteIntegrable := (exponential.continuousOn.mul
      ((leadingContinuous.add remainderContinuous).snd.abs.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
    have forcingIntegrable := (exponential.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc
      (μ := volume) inside.1
    rw [identity time inside]
    have absoluteBound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun current => Real.exp (-growth * (time - current)) * (leading current + remainder current).2) inside.1
    have comparison := intervalIntegral.integral_mono_on inside.1 absoluteIntegrable forcingIntegrable (by
      intro current member
      have projection : |(remainder current).2| ≤ ‖remainder current‖ := by
        simpa only [Real.norm_eq_abs] using norm_snd_le (remainder current)
      have sumBound : |(leading current + remainder current).2| ≤ forcing current :=
        (abs_add _ _).trans (add_le_add_left projection _)
      exact mul_le_mul_of_nonneg_left sumBound (Real.exp_pos _).le)
    have normalizedBound :
        |∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * (leading current + remainder current).2| ≤
          ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * |(leading current + remainder current).2| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using absoluteBound
    exact normalizedBound.trans comparison
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
    (relativeContinuous.snd.abs.intervalIntegrable_of_Icc finishNonnegative)
    (kernelContinuous.intervalIntegrable_of_Icc finishNonnegative) pointwise
  have convolution := EulerNonuniqueness.weighted_exponential_convolution_integral_le
    (rate := -growth) (weight := 0) forcingContinuous (by linarith only [growthPositive]) finishNonnegative
    (fun time _ => forcingNonnegative time)
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul, zero_sub, neg_neg] at convolution
  have normalized := (le_div_iff₀ growthPositive).mp (comparison.trans convolution)
  rw [intervalIntegral.integral_add
    (leadingContinuous.snd.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (remainderContinuous.norm.intervalIntegrable_of_Icc (μ := volume) finishNonnegative)] at normalized
  simpa only [mul_comm] using normalized

end EulerNonuniqueness.General
