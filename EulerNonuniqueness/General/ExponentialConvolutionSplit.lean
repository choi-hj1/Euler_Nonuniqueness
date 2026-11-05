import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Set MeasureTheory

namespace EulerNonuniqueness.General

/-- Splitting an exponential convolution preserves the original history, with its exact transport factor. -/
theorem exponential_convolution_split {function : ℝ → ℝ} {rate start cut finish : ℝ}
    (startCut : start ≤ cut) (cutFinish : cut ≤ finish)
    (integrable : IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * function time)
      volume start finish) :
    IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * function time) volume start cut ∧
    IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * function time) volume cut finish ∧
    IntervalIntegrable (fun time => Real.exp (rate * (cut - time)) * function time) volume start cut ∧
    (∫ time in start..finish, Real.exp (rate * (finish - time)) * function time) =
      Real.exp (rate * (finish - cut)) *
        (∫ time in start..cut, Real.exp (rate * (cut - time)) * function time) +
      (∫ time in cut..finish, Real.exp (rate * (finish - time)) * function time) := by
  have ordered : start ≤ finish := startCut.trans cutFinish
  have currentPrefix : IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * function time)
      volume start cut := by
    apply integrable.mono_set
    rw [uIcc_of_le startCut, uIcc_of_le ordered]
    exact Icc_subset_Icc le_rfl cutFinish
  have tail : IntervalIntegrable (fun time => Real.exp (rate * (finish - time)) * function time)
      volume cut finish := by
    apply integrable.mono_set
    rw [uIcc_of_le cutFinish, uIcc_of_le ordered]
    exact Icc_subset_Icc startCut le_rfl
  have oldIdentity : (fun time => Real.exp (rate * (cut - time)) * function time) =
      (fun time => Real.exp (-(rate * (finish - cut))) *
        (Real.exp (rate * (finish - time)) * function time)) := by
    funext time
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have oldPrefix : IntervalIntegrable (fun time => Real.exp (rate * (cut - time)) * function time)
      volume start cut := by
    rw [oldIdentity]
    exact currentPrefix.const_mul _
  have prefixIdentity :
      (∫ time in start..cut, Real.exp (rate * (finish - time)) * function time) =
        Real.exp (rate * (finish - cut)) *
          (∫ time in start..cut, Real.exp (rate * (cut - time)) * function time) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨currentPrefix, tail, oldPrefix, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals currentPrefix tail, prefixIdentity]

end EulerNonuniqueness.General
