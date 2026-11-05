import EulerNonuniqueness.General.WeightedResponseIntegral

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem weighted_response_integral_le_on_Icc
    {response forcing : ℝ → ℝ} {rate weight start finish : ℝ}
    (responseContinuous : ContinuousOn response (Icc start finish))
    (forcingContinuous : ContinuousOn forcing (Icc start finish))
    (equation : ∀ time ∈ Ioo start finish,
      HasDerivAt response (rate * response time + forcing time) time)
    (finalNonnegative : 0 ≤ response finish)
    (rateBound : rate < weight) (ordered : start ≤ finish) :
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * response time)
      volume start finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * forcing time)
      volume start finish ∧
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * response time) ≤
      (response start + ∫ time in start..finish,
        Real.exp (-weight * (time - start)) * forcing time) / (weight - rate) := by
  have kernelContinuous : Continuous (fun time : ℝ => Real.exp (-weight * (time - start))) := by
    fun_prop
  have responseIntegrable := (kernelContinuous.continuousOn.mul responseContinuous).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have forcingIntegrable := (kernelContinuous.continuousOn.mul forcingContinuous).intervalIntegrable_of_Icc
    (μ := volume) ordered
  have derivative (time : ℝ) (inside : time ∈ Ioo start finish) :
      HasDerivAt (fun current => Real.exp (-weight * (current - start)) * response current)
        ((rate - weight) * (Real.exp (-weight * (time - start)) * response time) +
          Real.exp (-weight * (time - start)) * forcing time) time := by
    convert ((((hasDerivAt_id time).sub_const start).const_mul (-weight)).exp).mul
      (equation time inside) using 1
    simp only [id_eq, mul_one]
    ring
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered
    (kernelContinuous.continuousOn.mul responseContinuous) derivative
    ((responseIntegrable.const_mul (rate - weight)).add forcingIntegrable)
  rw [intervalIntegral.integral_add (responseIntegrable.const_mul _) forcingIntegrable,
    intervalIntegral.integral_const_mul] at identity
  simp only [sub_self, mul_zero, Real.exp_zero, one_mul] at identity
  refine ⟨responseIntegrable, forcingIntegrable, (le_div_iff₀ (sub_pos.mpr rateBound)).mpr ?_⟩
  have endpointNonnegative := mul_nonneg (Real.exp_pos (-weight * (finish - start))).le finalNonnegative
  nlinarith only [identity, endpointNonnegative]

theorem weighted_retained_exponential_convolution_integral_le
    {forcing : ℝ → ℝ} {rate weight start finish : ℝ}
    (forcingContinuous : ContinuousOn forcing (Icc 0 finish))
    (forcingNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ forcing time)
    (startNonnegative : 0 ≤ start) (ordered : start ≤ finish) (rateBound : rate < weight) :
    let response := fun time => ∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * response time)
      volume start finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * (time - start)) * forcing time)
      volume start finish ∧
    (∫ time in start..finish, Real.exp (-weight * (time - start)) * response time) ≤
      (response start + ∫ time in start..finish,
        Real.exp (-weight * (time - start)) * forcing time) / (weight - rate) := by
  dsimp only
  have finishNonnegative : 0 ≤ finish := startNonnegative.trans ordered
  let extended := fun time : ℝ => forcing (projIcc 0 finish finishNonnegative time)
  have extendedContinuous : Continuous extended :=
    (continuousOn_iff_continuous_restrict.mp forcingContinuous).comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 finish) : extended time = forcing time := by
    simp only [extended, projIcc_of_mem finishNonnegative inside]
  have responseAgreement (time : ℝ) (inside : time ∈ Icc 0 finish) :
      exponentialResponse rate extended time = ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * forcing current := by
    rw [exponentialResponse_eq_integral]
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    change Real.exp (rate * (time - current)) * extended current = _
    rw [agreement current ⟨member.1, member.2.trans inside.2⟩]
  have extendedNonnegative : ∀ time ∈ Icc 0 finish, 0 ≤ extended time := by
    intro time inside
    rw [agreement time inside]
    exact forcingNonnegative time inside
  have responseContinuous : Continuous (exponentialResponse rate extended) :=
    continuous_iff_continuousAt.mpr fun time =>
      (hasDerivAt_exponentialResponse extendedContinuous rate time).continuousAt
  have estimate := weighted_response_integral_le_on_Icc responseContinuous.continuousOn
    extendedContinuous.continuousOn
    (fun time _ => hasDerivAt_exponentialResponse extendedContinuous rate time)
    (exponentialResponse_nonnegative finishNonnegative extendedNonnegative) rateBound ordered
  have subset : Icc start finish ⊆ Icc 0 finish := Icc_subset_Icc startNonnegative le_rfl
  have responseEqual : ∀ time ∈ uIcc start finish,
      Real.exp (-weight * (time - start)) * exponentialResponse rate extended time =
        Real.exp (-weight * (time - start)) *
          ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current := by
    intro time inside
    rw [uIcc_of_le ordered] at inside
    rw [responseAgreement time (subset inside)]
  have forcingEqual : ∀ time ∈ uIcc start finish,
      Real.exp (-weight * (time - start)) * extended time =
        Real.exp (-weight * (time - start)) * forcing time := by
    intro time inside
    rw [uIcc_of_le ordered] at inside
    rw [agreement time (subset inside)]
  refine ⟨estimate.1.congr (ae_restrict_of_forall_mem measurableSet_uIoc
    (fun time inside => responseEqual time (uIoc_subset_uIcc inside))),
    estimate.2.1.congr (ae_restrict_of_forall_mem measurableSet_uIoc
      (fun time inside => forcingEqual time (uIoc_subset_uIcc inside))), ?_⟩
  rw [intervalIntegral.integral_congr responseEqual, intervalIntegral.integral_congr forcingEqual,
    responseAgreement start ⟨startNonnegative, ordered⟩] at estimate
  exact estimate.2.2

end EulerNonuniqueness
