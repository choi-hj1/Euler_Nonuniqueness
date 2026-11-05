import EulerNonuniqueness.General.CommonLpLimit
import EulerNonuniqueness.General.SupportedLpSeries

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem exists_supported_all_finiteLp_limit
    {Domain : Type*} [TopologicalSpace Domain] [T2Space Domain] [MeasurableSpace Domain]
    {measure : Measure Domain} {sequence : ℕ → Domain → ℝ}
    (integrable : ∀ index, Integrable (sequence index) measure)
    (possible : ∀ exponent : ℝ, 1 ≤ exponent → ∃ limit : Domain → ℝ,
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure) atTop (𝓝 0))
    {region : Set Domain} (compact : IsCompact region)
    (supported : ∀ index, Function.support (sequence index) ⊆ region)
    (zeroMean : ∀ index, (∫ point, sequence index point ∂measure) = 0) :
    ∃ limit : Domain → ℝ, HasCompactSupport limit ∧ Function.support limit ⊆ region ∧
      (∫ point, limit point ∂measure) = 0 ∧
      ∀ exponent : ℝ, 1 ≤ exponent → MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  obtain ⟨raw, rawProperties⟩ := exists_common_limit_of_all_finiteLp_limits
    (fun index => (integrable index).aestronglyMeasurable) possible
  have rawOne : MemLp raw 1 measure := by simpa only [ENNReal.ofReal_one] using (rawProperties 1 le_rfl).1
  have rawConverges : Tendsto (fun index => eLpNorm (sequence index - raw) 1 measure) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_one] using (rawProperties 1 le_rfl).2
  let limit := region.indicator raw
  have equal : raw =ᵐ[measure] limit :=
    ae_eq_indicator_of_tendsto_eLpNorm_sub_of_support (by norm_num)
      (fun index => (integrable index).aestronglyMeasurable) rawOne.aestronglyMeasurable supported rawConverges
  have properties (exponent : ℝ) (exponentBound : 1 ≤ exponent) :
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
    refine ⟨(memLp_congr_ae equal).mp (rawProperties exponent exponentBound).1, ?_⟩
    have normEqual (index : ℕ) : eLpNorm (sequence index - raw) (ENNReal.ofReal exponent) measure =
        eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure := by
      apply eLpNorm_congr_ae
      filter_upwards [equal] with point equality
      simp only [Pi.sub_apply, equality]
    simpa only [normEqual] using (rawProperties exponent exponentBound).2
  have limitIntegrable : Integrable limit measure := memLp_one_iff_integrable.mp
    (by simpa only [ENNReal.ofReal_one] using (properties 1 le_rfl).1)
  have integralConverges := tendsto_integral_of_L1' limit limitIntegrable
    (Eventually.of_forall integrable) (by simpa only [ENNReal.ofReal_one] using (properties 1 le_rfl).2)
  have meanZero : (∫ point, limit point ∂measure) = 0 :=
    tendsto_nhds_unique (by simpa only [zeroMean] using integralConverges) tendsto_const_nhds
  exact ⟨limit, HasCompactSupport.of_support_subset_isCompact compact support_indicator_subset,
    support_indicator_subset, meanZero, properties⟩

end MeasureTheory
