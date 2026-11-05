import EulerNonuniqueness.General.WeightedResponseIntegral
import Mathlib.Analysis.Normed.Group.Constructions

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem saddle_history_norm_volterra
    {relative leading remainder : ℝ → ℝ × ℝ} {growth finish : ℝ}
    (growthNonnegative : 0 ≤ growth) (finishNonnegative : 0 ≤ finish)
    (relativeContinuous : ContinuousOn relative (Icc 0 finish))
    (leadingContinuous : ContinuousOn leading (Icc 0 finish))
    (remainderContinuous : ContinuousOn remainder (Icc 0 finish))
    (unstableHistory : ∀ time ∈ Icc 0 finish,
      Real.exp (-growth * time) * (relative time).1 =
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current + remainder current).1)
    (stableHistory : ∀ time ∈ Icc 0 finish,
      (relative time).2 = ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (leading current + remainder current).2) :
    relative 0 = 0 ∧
    ∀ time ∈ Icc 0 finish,
      IntervalIntegrable (fun current => |(relative current).1| + |(relative current).2|) volume 0 time ∧
      IntervalIntegrable (fun current => Real.exp (growth * (time - current)) *
        (‖leading current‖ + ‖remainder current‖)) volume 0 time ∧
      |(relative time).1| + |(relative time).2| ≤
        2 * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
          (‖leading current‖ + ‖remainder current‖) := by
  have initial : relative 0 = 0 := by
    apply Prod.ext
    · simpa only [mul_zero, Real.exp_zero, one_mul, intervalIntegral.integral_same, Prod.fst_zero] using
        unstableHistory 0 ⟨le_rfl, finishNonnegative⟩
    · simpa only [intervalIntegral.integral_same, Prod.snd_zero] using
        stableHistory 0 ⟨le_rfl, finishNonnegative⟩
  refine ⟨initial, ?_⟩
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have inputContinuous := (leadingContinuous.add remainderContinuous).mono subset
  have forcingContinuous := (leadingContinuous.norm.add remainderContinuous.norm).mono subset
  have positiveKernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by fun_prop
  have negativeKernel : Continuous (fun current : ℝ => Real.exp (-growth * (time - current))) := by fun_prop
  have majorantIntegrable := (positiveKernel.continuousOn.mul forcingContinuous).intervalIntegrable_of_Icc (μ := volume) inside.1
  have unstableAbsoluteIntegrable :=
    (positiveKernel.continuousOn.mul inputContinuous.fst.abs).intervalIntegrable_of_Icc (μ := volume) inside.1
  have stableAbsoluteIntegrable :=
    (negativeKernel.continuousOn.mul inputContinuous.snd.abs).intervalIntegrable_of_Icc (μ := volume) inside.1
  have unstableIdentity : (relative time).1 = ∫ current in (0 : ℝ)..time,
      Real.exp (growth * (time - current)) * (leading current + remainder current).1 := by
    have cancellation : Real.exp (growth * time) * Real.exp (-growth * time) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    calc
      (relative time).1 = Real.exp (growth * time) * (Real.exp (-growth * time) * (relative time).1) := by
        rw [← mul_assoc, cancellation, one_mul]
      _ = Real.exp (growth * time) * ∫ current in (0 : ℝ)..time,
          Real.exp (-growth * current) * (leading current + remainder current).1 := by rw [unstableHistory time inside]
      _ = _ := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro current _
        change Real.exp (growth * time) * (Real.exp (-growth * current) * (leading current + remainder current).1) =
          Real.exp (growth * (time - current)) * (leading current + remainder current).1
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
  have firstProjection (current : ℝ) :
      |(leading current + remainder current).1| ≤ ‖leading current‖ + ‖remainder current‖ := by
    have projection : |(leading current + remainder current).1| ≤ ‖leading current + remainder current‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (leading current + remainder current)
    exact projection.trans (norm_add_le _ _)
  have secondProjection (current : ℝ) :
      |(leading current + remainder current).2| ≤ ‖leading current‖ + ‖remainder current‖ := by
    have projection : |(leading current + remainder current).2| ≤ ‖leading current + remainder current‖ := by
      simpa only [Real.norm_eq_abs] using norm_snd_le (leading current + remainder current)
    exact projection.trans (norm_add_le _ _)
  have unstableBound : |(relative time).1| ≤ ∫ current in (0 : ℝ)..time,
      Real.exp (growth * (time - current)) * (‖leading current‖ + ‖remainder current‖) := by
    rw [unstableIdentity]
    have absoluteBound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun current => Real.exp (growth * (time - current)) * (leading current + remainder current).1) inside.1
    have normalized : |∫ current in (0 : ℝ)..time,
        Real.exp (growth * (time - current)) * (leading current + remainder current).1| ≤
        ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) * |(leading current + remainder current).1| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using absoluteBound
    exact normalized.trans (intervalIntegral.integral_mono_on inside.1 unstableAbsoluteIntegrable majorantIntegrable
      (fun current _ => mul_le_mul_of_nonneg_left (firstProjection current) (Real.exp_pos _).le))
  have stableBound : |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
      Real.exp (growth * (time - current)) * (‖leading current‖ + ‖remainder current‖) := by
    rw [stableHistory time inside]
    have absoluteBound := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
      (f := fun current => Real.exp (-growth * (time - current)) * (leading current + remainder current).2) inside.1
    have normalized : |∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (leading current + remainder current).2| ≤
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * (time - current)) * |(leading current + remainder current).2| := by
      simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using absoluteBound
    apply normalized.trans
    apply intervalIntegral.integral_mono_on inside.1 stableAbsoluteIntegrable majorantIntegrable
    intro current member
    have exponentBound : -growth * (time - current) ≤ growth * (time - current) := by
      nlinarith only [mul_nonneg growthNonnegative (sub_nonneg.mpr member.2)]
    exact mul_le_mul (Real.exp_le_exp.mpr exponentBound) (secondProjection current) (abs_nonneg _) (Real.exp_pos _).le
  refine ⟨((relativeContinuous.fst.abs.add relativeContinuous.snd.abs).mono subset).intervalIntegrable_of_Icc inside.1,
    majorantIntegrable, ?_⟩
  linarith only [unstableBound, stableBound]

end EulerNonuniqueness.General
