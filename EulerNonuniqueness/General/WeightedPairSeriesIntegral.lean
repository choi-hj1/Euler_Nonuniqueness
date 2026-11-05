import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace EulerNonuniqueness.General

theorem intervalIntegrable_weighted_pair_tsum_of_integrable_sides
    {Value : Type*} [NormedAddCommGroup Value]
    {first second : ℕ → ℝ → Value} {sequenceWeight : ℕ → ℝ} {timeWeight : ℝ → ℝ}
    {start finish : ℝ} {measure : Measure ℝ}
    (ordered : start ≤ finish)
    (firstContinuous : ∀ index, ContinuousOn (first index) (Icc start finish))
    (secondContinuous : ∀ index, ContinuousOn (second index) (Icc start finish))
    (sequenceNonnegative : ∀ index, 0 ≤ sequenceWeight index)
    (timeContinuous : ContinuousOn timeWeight (Icc start finish))
    (timeNonnegative : ∀ time ∈ Icc start finish, 0 ≤ timeWeight time)
    (firstSummable : ∀ time ∈ Icc start finish, Summable (fun index => sequenceWeight index * ‖first index time‖))
    (secondSummable : ∀ time ∈ Icc start finish, Summable (fun index => sequenceWeight index * ‖second index time‖))
    (firstIntegrable : IntervalIntegrable
      (fun time => timeWeight time * ∑' index, sequenceWeight index * ‖first index time‖) measure start finish)
    (secondIntegrable : IntervalIntegrable
      (fun time => timeWeight time * ∑' index, sequenceWeight index * ‖second index time‖) measure start finish) :
    (∀ time ∈ Icc start finish, Summable (fun index => sequenceWeight index * ‖first index time - second index time‖)) ∧
      IntervalIntegrable
        (fun time => timeWeight time * ∑' index, sequenceWeight index * ‖first index time - second index time‖)
        measure start finish ∧
      (∫ time in start..finish, timeWeight time * ∑' index, sequenceWeight index * ‖first index time - second index time‖ ∂measure) ≤
        (∫ time in start..finish, timeWeight time * ∑' index, sequenceWeight index * ‖first index time‖ ∂measure) +
          (∫ time in start..finish, timeWeight time * ∑' index, sequenceWeight index * ‖second index time‖ ∂measure) := by
  let terms := fun index time => sequenceWeight index * ‖first index time - second index time‖
  have termsNonnegative (index : ℕ) (time : ℝ) : 0 ≤ terms index time :=
    mul_nonneg (sequenceNonnegative index) (norm_nonneg _)
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) :
      Summable (fun index => terms index time) ∧
        (∑' index, terms index time) ≤ (∑' index, sequenceWeight index * ‖first index time‖) +
          ∑' index, sequenceWeight index * ‖second index time‖ := by
    have bound (index : ℕ) : terms index time ≤ sequenceWeight index * ‖first index time‖ +
        sequenceWeight index * ‖second index time‖ := by
      exact (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (sequenceNonnegative index)).trans_eq (mul_add _ _ _)
    have majorant := (firstSummable time inside).add (secondSummable time inside)
    have summable := Summable.of_nonneg_of_le (fun index => termsNonnegative index time) bound majorant
    refine ⟨summable, ?_⟩
    have estimate := summable.tsum_le_tsum bound majorant
    rw [(firstSummable time inside).tsum_add (secondSummable time inside)] at estimate
    exact estimate
  have intervalSubset : Ι start finish ⊆ Icc start finish := by
    rw [uIoc_of_le ordered]
    exact Ioc_subset_Icc_self
  have termsContinuous (index : ℕ) : ContinuousOn (terms index) (Icc start finish) :=
    continuousOn_const.mul ((firstContinuous index).sub (secondContinuous index)).norm
  have partialMeasurable (count : ℕ) :
      AEStronglyMeasurable (fun time => ∑ index ∈ Finset.range count, terms index time)
        (measure.restrict (Ι start finish)) := by
    have regular : ContinuousOn (fun time => ∑ index ∈ Finset.range count, terms index time) (Icc start finish) :=
      continuousOn_finset_sum _ (fun index _ => termsContinuous index)
    exact AEStronglyMeasurable.mono_set intervalSubset (regular.aestronglyMeasurable measurableSet_Icc)
  have seriesMeasurable : AEStronglyMeasurable (fun time => ∑' index, terms index time)
      (measure.restrict (Ι start finish)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop partialMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    exact (pointwise time (intervalSubset inside)).1.hasSum.tendsto_sum_nat
  have timeMeasurable : AEStronglyMeasurable timeWeight (measure.restrict (Ι start finish)) :=
    AEStronglyMeasurable.mono_set intervalSubset (timeContinuous.aestronglyMeasurable measurableSet_Icc)
  have weightedBound (time : ℝ) (inside : time ∈ Icc start finish) :
      timeWeight time * (∑' index, terms index time) ≤
        timeWeight time * (∑' index, sequenceWeight index * ‖first index time‖) +
          timeWeight time * (∑' index, sequenceWeight index * ‖second index time‖) :=
    (mul_le_mul_of_nonneg_left (pointwise time inside).2 (timeNonnegative time inside)).trans_eq (mul_add _ _ _)
  have majorantIntegrable := firstIntegrable.add secondIntegrable
  have integrable := majorantIntegrable.mono_fun' (timeMeasurable.mul seriesMeasurable) (by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    have member := intervalSubset inside
    change ‖timeWeight time * (∑' index, terms index time)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (timeNonnegative time member)
      (tsum_nonneg (fun index => termsNonnegative index time)))]
    exact weightedBound time member)
  have estimate := intervalIntegral.integral_mono_on ordered integrable majorantIntegrable weightedBound
  rw [intervalIntegral.integral_add firstIntegrable secondIntegrable] at estimate
  exact ⟨fun time inside => (pointwise time inside).1, integrable, estimate⟩

end EulerNonuniqueness.General
