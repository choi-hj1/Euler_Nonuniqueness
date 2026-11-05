import EulerNonuniqueness.General.TwoRateExponentialResponse

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem switched_stable_convolution_bound
    {forcing : ℝ → ℝ} {finish entry decay beta incoming slope offset : ℝ}
    (entryNonnegative : 0 ≤ entry) (entryBefore : entry ≤ finish)
    (decayPositive : 0 < decay) (gapPositive : 0 < beta + decay)
    (incomingNonnegative : 0 ≤ incoming) (slopeNonnegative : 0 ≤ slope)
    (offsetNonnegative : 0 ≤ offset)
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (incomingBound : ∀ time ∈ Icc 0 entry,
      forcing time ≤ incoming * Real.exp (beta * (time - entry)))
    (outgoingBound : ∀ time ∈ Ioc entry finish,
      forcing time ≤ slope * (time - entry) + offset) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-decay * (finish - time)) * forcing time) ≤
      incoming / (beta + decay) * Real.exp (-decay * (finish - entry)) +
        (slope * (finish - entry) + offset) / decay := by
  have kernel : Continuous (fun time : ℝ => Real.exp (-decay * (finish - time))) := by fun_prop
  have beforeSubset : Icc (0 : ℝ) entry ⊆ Icc 0 finish := Icc_subset_Icc le_rfl entryBefore
  have afterSubset : Icc entry finish ⊆ Icc 0 finish := Icc_subset_Icc entryNonnegative le_rfl
  have beforeIntegrable := (kernel.continuousOn.mul (forcingContinuous.mono beforeSubset)).intervalIntegrable_of_Icc
    (μ := volume) entryNonnegative
  have afterIntegrable := (kernel.continuousOn.mul (forcingContinuous.mono afterSubset)).intervalIntegrable_of_Icc
    (μ := volume) entryBefore
  have weightedIntegrable := (((by fun_prop : Continuous (fun time : ℝ => Real.exp (-(-decay) * time)))).continuousOn.mul
    (forcingContinuous.mono beforeSubset)).intervalIntegrable_of_Icc (μ := volume) entryNonnegative
  have pre := intervalIntegral.exp_mul_integral_le_of_faster_exponential_majorant
    (firstRate := -decay) (secondRate := beta) entryNonnegative (by linarith only [gapPositive])
    incomingNonnegative weightedIntegrable incomingBound
  have factorization (time : ℝ) :
      Real.exp (-decay * (finish - time)) =
        Real.exp (-decay * (finish - entry)) *
          (Real.exp (-decay * entry) * Real.exp (-(-decay) * time)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have preIdentity :
      (∫ time in (0 : ℝ)..entry, Real.exp (-decay * (finish - time)) * forcing time) =
        Real.exp (-decay * (finish - entry)) *
          (Real.exp (-decay * entry) * ∫ time in (0 : ℝ)..entry, Real.exp (-(-decay) * time) * forcing time) := by
    rw [← mul_assoc, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    rw [factorization time]
    ring
  have preBound :
      (∫ time in (0 : ℝ)..entry, Real.exp (-decay * (finish - time)) * forcing time) ≤
        incoming / (beta + decay) * Real.exp (-decay * (finish - entry)) := by
    rw [preIdentity]
    have bound := mul_le_mul_of_nonneg_left pre (Real.exp_pos (-decay * (finish - entry))).le
    simpa only [sub_self, mul_zero, Real.exp_zero, mul_one, sub_neg_eq_add, mul_comm] using bound
  have kernelIntegrable : IntervalIntegrable
      (fun time : ℝ => Real.exp (-decay * (finish - time))) volume entry finish :=
    kernel.intervalIntegrable entry finish
  have massIdentity : (∫ time in entry..finish, Real.exp (-decay * (finish - time))) =
      (1 - Real.exp (-decay * (finish - entry))) / decay := by
    have pointwise : (fun time : ℝ => Real.exp (-decay * (finish - time))) =
        (fun time => Real.exp (decay * time + (-decay * finish))) := by
      funext time
      congr 1
      ring
    rw [pointwise, intervalIntegral.integral_comp_mul_add Real.exp decayPositive.ne', integral_exp]
    have atFinish : decay * finish + -decay * finish = 0 := by ring
    have atEntry : decay * entry + -decay * finish = -decay * (finish - entry) := by ring
    rw [atFinish, atEntry, Real.exp_zero]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have massBound : (∫ time in entry..finish, Real.exp (-decay * (finish - time))) ≤ 1 / decay := by
    rw [massIdentity]
    apply div_le_div_of_nonneg_right _ decayPositive.le
    linarith only [Real.exp_pos (-decay * (finish - entry))]
  have terminalNonnegative : 0 ≤ slope * (finish - entry) + offset :=
    add_nonneg (mul_nonneg slopeNonnegative (sub_nonneg.mpr entryBefore)) offsetNonnegative
  have upperIntegrable := kernelIntegrable.mul_const (slope * (finish - entry) + offset)
  have postComparison := intervalIntegral.integral_mono_on_of_le_Ioo entryBefore afterIntegrable upperIntegrable (by
    intro time member
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact (outgoingBound time ⟨member.1, member.2.le⟩).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (by linarith only [member.2]) slopeNonnegative) offset))
  rw [intervalIntegral.integral_mul_const] at postComparison
  have postBound := postComparison.trans (mul_le_mul_of_nonneg_right massBound terminalNonnegative)
  rw [← intervalIntegral.integral_add_adjacent_intervals beforeIntegrable afterIntegrable]
  have normalizedPost :
      (∫ time in entry..finish, Real.exp (-decay * (finish - time)) * forcing time) ≤
        (slope * (finish - entry) + offset) / decay := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using postBound
  exact add_le_add preBound normalizedPost

end EulerNonuniqueness.General
