import Mathlib

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators Interval

namespace EulerNonuniqueness.General

theorem intervalIntegrable_weighted_tsum_of_continuousOn_majorant
    {terms : ℕ → ℝ → ℝ} {weight majorant : ℝ → ℝ} {start finish : ℝ}
    (ordered : start ≤ finish)
    (termsContinuous : ∀ index, ContinuousOn (terms index) (Icc start finish))
    (termsNonnegative : ∀ index, ∀ time ∈ Icc start finish, 0 ≤ terms index time)
    (termsSummable : ∀ time ∈ Icc start finish, Summable (fun index => terms index time))
    (weightContinuous : ContinuousOn weight (Icc start finish))
    (weightNonnegative : ∀ time ∈ Icc start finish, 0 ≤ weight time)
    (majorantContinuous : ContinuousOn majorant (Icc start finish))
    (bounded : ∀ time ∈ Icc start finish, (∑' index, terms index time) ≤ majorant time) :
    IntervalIntegrable (fun time => weight time * ∑' index, terms index time) volume start finish ∧
      (∫ time in start..finish, weight time * ∑' index, terms index time) ≤
        ∫ time in start..finish, weight time * majorant time := by
  have intervalSubset : Ι start finish ⊆ Icc start finish := by
    rw [uIoc_of_le ordered]
    exact Ioc_subset_Icc_self
  have partialMeasurable (count : ℕ) :
      AEStronglyMeasurable (fun time => ∑ index ∈ Finset.range count, terms index time)
        (volume.restrict (Ι start finish)) := by
    have regular : ContinuousOn (fun time => ∑ index ∈ Finset.range count, terms index time) (Icc start finish) :=
      continuousOn_finset_sum _ (fun index _ => termsContinuous index)
    exact AEStronglyMeasurable.mono_set intervalSubset (regular.aestronglyMeasurable measurableSet_Icc)
  have seriesMeasurable : AEStronglyMeasurable (fun time => ∑' index, terms index time)
      (volume.restrict (Ι start finish)) := by
    apply aestronglyMeasurable_of_tendsto_ae atTop partialMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    exact (termsSummable time (intervalSubset inside)).hasSum.tendsto_sum_nat
  have weightMeasurable : AEStronglyMeasurable weight (volume.restrict (Ι start finish)) :=
    AEStronglyMeasurable.mono_set intervalSubset (weightContinuous.aestronglyMeasurable measurableSet_Icc)
  have majorantIntegrable := (weightContinuous.mul majorantContinuous).intervalIntegrable_of_Icc (μ := volume) ordered
  have pointwise (time : ℝ) (inside : time ∈ Icc start finish) :
      weight time * (∑' index, terms index time) ≤ weight time * majorant time :=
    mul_le_mul_of_nonneg_left (bounded time inside) (weightNonnegative time inside)
  have integrable := majorantIntegrable.mono_fun' (weightMeasurable.mul seriesMeasurable) (by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with time inside
    have member := intervalSubset inside
    change ‖weight time * (∑' index, terms index time)‖ ≤ weight time * majorant time
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weightNonnegative time member)
      (tsum_nonneg (fun index => termsNonnegative index time member)))]
    exact pointwise time member)
  exact ⟨integrable, intervalIntegral.integral_mono_on ordered integrable majorantIntegrable pointwise⟩

end EulerNonuniqueness.General
