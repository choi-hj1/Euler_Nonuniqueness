import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Set MeasureTheory

namespace intervalIntegral

theorem integral_primitive_eq_integral_remaining_mul
    {forcing : ℝ → ℝ} {lower upper : ℝ} (ordered : lower ≤ upper)
    (forcingContinuous : ContinuousOn forcing (Icc lower upper)) :
    (∫ time in lower..upper, ∫ current in lower..time, forcing current) =
      ∫ time in lower..upper, (upper - time) * forcing time := by
  let primitive : ℝ → ℝ := fun time => ∫ current in lower..time, forcing current
  have forcingUnordered : ContinuousOn forcing (uIcc lower upper) := by
    simpa only [uIcc_of_le ordered] using forcingContinuous
  have forcingIntegrable := forcingUnordered.intervalIntegrable (μ := volume)
  have primitiveContinuous : ContinuousOn primitive (uIcc lower upper) :=
    continuousOn_primitive_interval' forcingIntegrable left_mem_uIcc
  have weightContinuous : ContinuousOn (fun time : ℝ => upper - time) (uIcc lower upper) := by
    fun_prop
  have weightDerivative (time : ℝ) : HasDerivAt (fun current : ℝ => upper - current) (-1) time := by
    simpa only [zero_sub] using (hasDerivAt_const time upper).sub (hasDerivAt_id time)
  have primitiveDerivative (time : ℝ) (inside : time ∈ Ioo lower upper) :
      HasDerivAt primitive (forcing time) time := by
    have forcingInterior := forcingContinuous.mono Ioo_subset_Icc_self
    have measurable := ContinuousOn.stronglyMeasurableAtFilter (μ := volume)
      isOpen_Ioo forcingInterior time inside
    have atTime := forcingInterior.continuousAt (isOpen_Ioo.mem_nhds inside)
    have integrable := forcingIntegrable.mono_set (show uIcc lower time ⊆ uIcc lower upper by
      rw [uIcc_of_le inside.1.le, uIcc_of_le ordered]
      exact Icc_subset_Icc le_rfl inside.2.le)
    exact integral_hasDerivAt_right integrable measurable atTime
  have identity := integral_mul_deriv_eq_deriv_mul_of_hasDerivAt weightContinuous primitiveContinuous
    (fun time _ => weightDerivative time)
    (by simpa only [min_eq_left ordered, max_eq_right ordered] using primitiveDerivative)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ)) volume lower upper)
    forcingIntegrable
  have primitiveInitial : primitive lower = 0 := integral_same
  simp only [sub_self, zero_mul, primitiveInitial, mul_zero, sub_zero, zero_sub, neg_one_mul, integral_neg,
    neg_neg] at identity
  exact identity.symm

theorem integral_history_le_integral_remaining_forcing
    {history forcing : ℝ → ℝ} {lower upper : ℝ} (ordered : lower ≤ upper)
    (historyContinuous : ContinuousOn history (Icc lower upper))
    (forcingContinuous : ContinuousOn forcing (Icc lower upper))
    (historyBound : ∀ time ∈ Icc lower upper,
      history time ≤ ∫ current in lower..time, forcing current) :
    (∫ time in lower..upper, history time) ≤
      ∫ time in lower..upper, (upper - time) * forcing time := by
  have forcingIntegrable := forcingContinuous.intervalIntegrable_of_Icc (μ := volume) ordered
  have primitiveContinuous := continuousOn_primitive_interval' forcingIntegrable left_mem_uIcc
  have comparison := integral_mono_on ordered
    (historyContinuous.intervalIntegrable_of_Icc (μ := volume) ordered)
    primitiveContinuous.intervalIntegrable historyBound
  exact comparison.trans_eq (integral_primitive_eq_integral_remaining_mul ordered forcingContinuous)

end intervalIntegral
