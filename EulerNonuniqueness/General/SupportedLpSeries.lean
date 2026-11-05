import EulerNonuniqueness.General.LpSeries

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace MeasureTheory

theorem ae_eq_indicator_of_tendsto_eLpNorm_sub_of_support
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {sequence : ℕ → Domain → Value} {limit : Domain → Value}
    {exponent : ℝ≥0∞} (nonzero : exponent ≠ 0)
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    (limitMeasurable : AEStronglyMeasurable limit measure)
    {region : Set Domain} (supported : ∀ index, Function.support (sequence index) ⊆ region)
    (converges : Tendsto (fun index => eLpNorm (sequence index - limit) exponent measure) atTop (𝓝 0)) :
    limit =ᵐ[measure] region.indicator limit := by
  obtain ⟨subsequence, increasing, almostEverywhere⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm nonzero measurable limitMeasurable converges).exists_seq_tendsto_ae
  filter_upwards [almostEverywhere] with point convergence
  by_cases inside : point ∈ region
  · simp only [indicator_of_mem inside]
  · have zero (index : ℕ) : sequence (subsequence index) point = 0 :=
      Function.nmem_support.mp fun inSupport => inside (supported (subsequence index) inSupport)
    have limitZero : limit point = 0 :=
      tendsto_nhds_unique (by simpa only [zero] using convergence) tendsto_const_nhds
    simp only [limitZero, indicator_of_not_mem inside]

theorem exists_supported_all_finiteLp_limit_of_summable_eLpNorm
    {Domain : Type*} [TopologicalSpace Domain] [T2Space Domain] [MeasurableSpace Domain]
    {measure : Measure Domain} {fields : ℕ → Domain → ℝ}
    (members : ∀ exponent : ℝ, 1 ≤ exponent → ∀ index,
      MemLp (fields index) (ENNReal.ofReal exponent) measure)
    (summable : ∀ exponent : ℝ, 1 ≤ exponent →
      Summable (fun index => (eLpNorm (fields index) (ENNReal.ofReal exponent) measure).toReal))
    {region : Set Domain} (compact : IsCompact region)
    (supported : ∀ index, Function.support (fields index) ⊆ region)
    (zeroMean : ∀ index, (∫ point, fields index point ∂measure) = 0) :
    ∃ limit : Domain → ℝ, HasCompactSupport limit ∧ Function.support limit ⊆ region ∧
      (∫ point, limit point ∂measure) = 0 ∧
      ∀ exponent : ℝ, 1 ≤ exponent → MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun count => eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit)
          (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  obtain ⟨raw, rawProperties⟩ := exists_all_finiteLp_limit_of_summable_eLpNorm members summable
  have oneMembers : ∀ index, MemLp (fields index) 1 measure := by
    simpa only [ENNReal.ofReal_one] using members 1 le_rfl
  have rawOne : MemLp raw 1 measure := by simpa only [ENNReal.ofReal_one] using (rawProperties 1 le_rfl).1
  have rawConverges : Tendsto
      (fun count => eLpNorm ((∑ index ∈ Finset.range count, fields index) - raw) 1 measure) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_one] using (rawProperties 1 le_rfl).2
  have partialSupported (count : ℕ) :
      Function.support (∑ index ∈ Finset.range count, fields index) ⊆ region := by
    intro point nonzero
    by_contra outside
    have zero (index : ℕ) : fields index point = 0 :=
      Function.nmem_support.mp fun inside => outside (supported index inside)
    exact nonzero (by simp only [Finset.sum_apply, zero, Finset.sum_const_zero])
  let limit := region.indicator raw
  have equal : raw =ᵐ[measure] limit :=
    ae_eq_indicator_of_tendsto_eLpNorm_sub_of_support (by norm_num)
      (fun count => (memLp_finset_sum' (Finset.range count)
        (fun index _ => oneMembers index)).aestronglyMeasurable)
      rawOne.aestronglyMeasurable partialSupported rawConverges
  have properties (exponent : ℝ) (exponentBound : 1 ≤ exponent) :
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun count => eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit)
          (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
    refine ⟨(memLp_congr_ae equal).mp (rawProperties exponent exponentBound).1, ?_⟩
    have normEqual (count : ℕ) :
        eLpNorm ((∑ index ∈ Finset.range count, fields index) - raw) (ENNReal.ofReal exponent) measure =
        eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit) (ENNReal.ofReal exponent) measure := by
      apply eLpNorm_congr_ae
      filter_upwards [equal] with point equality
      simp only [Pi.sub_apply, equality]
    simpa only [normEqual] using (rawProperties exponent exponentBound).2
  have limitIntegrable : Integrable limit measure := memLp_one_iff_integrable.mp
    (by simpa only [ENNReal.ofReal_one] using (properties 1 le_rfl).1)
  have integralConverges := tendsto_integral_of_L1' limit limitIntegrable
    (Eventually.of_forall fun count => memLp_one_iff_integrable.mp
      (memLp_finset_sum' (Finset.range count) (fun index _ => oneMembers index)))
    (by simpa only [ENNReal.ofReal_one] using (properties 1 le_rfl).2)
  have integralZero (count : ℕ) : (∫ point, (∑ index ∈ Finset.range count, fields index) point ∂measure) = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finset_sum _ (fun index _ => memLp_one_iff_integrable.mp (oneMembers index))]
    simp only [zeroMean, Finset.sum_const_zero]
  have meanZero : (∫ point, limit point ∂measure) = 0 :=
    tendsto_nhds_unique (by simpa only [integralZero] using integralConverges) tendsto_const_nhds
  exact ⟨limit, HasCompactSupport.of_support_subset_isCompact compact support_indicator_subset,
    support_indicator_subset, meanZero, properties⟩

end MeasureTheory
