import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem stable_volterra_feedback_absorption
    {stable forcing coefficient : ℝ → ℝ} {decay finish : ℝ}
    (finishNonnegative : 0 ≤ finish) (decayNonnegative : 0 ≤ decay)
    (stableContinuous : ContinuousOn stable (Icc 0 finish))
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 finish))
    (stableNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ stable time)
    (coefficientUpper : ∀ time ∈ Icc 0 finish, coefficient time ≤ decay / 2)
    (history : ∀ time ∈ Icc 0 finish,
      stable time ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-decay * (time - current)) *
          (coefficient current * stable current + forcing current)) :
    ∀ time ∈ Icc 0 finish,
      stable time ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-(decay / 2) * (time - current)) * forcing current := by
  have majorized : ∀ time ∈ Icc 0 finish, stable time ≤
      0 * Real.exp (-decay * time) + 1 * ∫ current in (0 : ℝ)..time,
        Real.exp (-decay * (time - current)) * (forcing current + decay / 2 * stable current) := by
    intro time inside
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernel : Continuous (fun current : ℝ => Real.exp (-decay * (time - current))) := by fun_prop
    have originalIntegrable := (kernel.continuousOn.mul
      ((coefficientContinuous.mul stableContinuous).add forcingContinuous |>.mono subset)).intervalIntegrable_of_Icc
      (μ := volume) inside.1
    have upperIntegrable := (kernel.continuousOn.mul
      ((forcingContinuous.add ((continuousOn_const (c := decay / 2)).mul stableContinuous)).mono subset)).intervalIntegrable_of_Icc
      (μ := volume) inside.1
    simp only [zero_mul, zero_add, one_mul]
    apply (history time inside).trans
    apply intervalIntegral.integral_mono_on inside.1 originalIntegrable upperIntegrable
    intro current member
    have currentInside := subset member
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have bound := mul_le_mul_of_nonneg_right (coefficientUpper current currentInside)
      (stableNonnegative current currentInside)
    linarith only [bound]
  have resolved := EulerNonuniqueness.exponential_volterra_gronwall stableContinuous forcingContinuous
    (show 0 ≤ decay / 2 by positivity) (show (0 : ℝ) ≤ 1 by norm_num) finishNonnegative majorized
  have rate : -decay + decay / 2 = -(decay / 2) := by ring
  simpa only [zero_mul, zero_add, one_mul, rate] using resolved

theorem stable_original_history_feedback_bound
    {relative leading remainder : ℝ → ℝ × ℝ} {coefficient additive : ℝ → ℝ}
    {decay finish : ℝ}
    (finishNonnegative : 0 ≤ finish) (decayNonnegative : 0 ≤ decay)
    (relativeContinuous : ContinuousOn relative (Icc 0 finish))
    (leadingContinuous : ContinuousOn leading (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 finish))
    (additiveContinuous : ContinuousOn additive (Icc 0 finish))
    (coefficientUpper : ∀ time ∈ Icc 0 finish, coefficient time ≤ decay / 2)
    (remainderBound : ∀ time ∈ Icc 0 finish,
      |(remainder time).2| ≤ coefficient time * |(relative time).2| + additive time)
    (history : ∀ time ∈ Icc 0 finish,
      (relative time).2 = ∫ current in (0 : ℝ)..time,
        Real.exp (-decay * (time - current)) * (leading current + remainder current).2) :
    ∀ time ∈ Icc 0 finish,
      |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-(decay / 2) * (time - current)) * (|(leading current).2| + additive current) := by
  apply stable_volterra_feedback_absorption finishNonnegative decayNonnegative
    relativeContinuous.snd.abs (leadingContinuous.snd.abs.add additiveContinuous) coefficientContinuous
    (fun _ _ => abs_nonneg _) coefficientUpper
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have kernel : Continuous (fun current : ℝ => Real.exp (-decay * (time - current))) := by fun_prop
  have originalIntegrable := (kernel.continuousOn.mul
    ((leadingContinuous.add remainderContinuous).snd.abs.mono subset)).intervalIntegrable_of_Icc
    (μ := volume) inside.1
  have upperIntegrable := (kernel.continuousOn.mul
    (((coefficientContinuous.mul relativeContinuous.snd.abs).add
      (leadingContinuous.snd.abs.add additiveContinuous)).mono subset)).intervalIntegrable_of_Icc
    (μ := volume) inside.1
  rw [history time inside]
  have absolute := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun current => Real.exp (-decay * (time - current)) * (leading current + remainder current).2) inside.1
  have normalized :
      |∫ current in (0 : ℝ)..time, Real.exp (-decay * (time - current)) * (leading current + remainder current).2| ≤
        ∫ current in (0 : ℝ)..time, Real.exp (-decay * (time - current)) * |(leading current + remainder current).2| := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using absolute
  apply normalized.trans
  apply intervalIntegral.integral_mono_on inside.1 originalIntegrable upperIntegrable
  intro current member
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have bound := (abs_add (leading current).2 (remainder current).2).trans
    (add_le_add_left (remainderBound current (subset member)) _)
  simpa only [Prod.snd_add] using bound.trans_eq (by ring)

end EulerNonuniqueness.General
