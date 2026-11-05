import EulerNonuniqueness.General.TriangularLpConvergence

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace MeasureTheory

theorem exists_common_limit_of_all_finiteLp_limits
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {sequence : ℕ → Domain → Value}
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    (possible : ∀ exponent : ℝ, 1 ≤ exponent → ∃ limit : Domain → Value,
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure) atTop (𝓝 0)) :
    ∃ limit : Domain → Value, ∀ exponent : ℝ, 1 ≤ exponent →
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  obtain ⟨limit, limitMember, oneConverges⟩ := possible 1 le_rfl
  refine ⟨limit, fun exponent exponentBound => ?_⟩
  obtain ⟨candidate, candidateMember, candidateConverges⟩ := possible exponent exponentBound
  have positive : 0 < ENNReal.ofReal exponent := ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le exponentBound)
  have equal : candidate =ᵐ[measure] limit :=
    ae_eq_of_tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub positive.ne' (by norm_num)
      measurable candidateMember.aestronglyMeasurable limitMember.aestronglyMeasurable
      candidateConverges oneConverges
  refine ⟨(memLp_congr_ae equal).mp candidateMember, ?_⟩
  have normEqual (index : ℕ) : eLpNorm (sequence index - candidate) (ENNReal.ofReal exponent) measure =
      eLpNorm (sequence index - limit) (ENNReal.ofReal exponent) measure := by
    apply eLpNorm_congr_ae
    filter_upwards [equal] with point equality
    simp only [Pi.sub_apply, equality]
  simpa only [normEqual] using candidateConverges

theorem exists_all_finiteLp_limit_of_dominated_triangular_sums
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value] [CompleteSpace Value]
    {measure : Measure Domain} {fields : ℕ → ℕ → Domain → Value} {limits : ℕ → Domain → Value}
    (members : ∀ exponent : ℝ, 1 ≤ exponent → ∀ step index,
      MemLp (fields step index) (ENNReal.ofReal exponent) measure)
    (limitMembers : ∀ exponent : ℝ, 1 ≤ exponent → ∀ index,
      MemLp (limits index) (ENNReal.ofReal exponent) measure)
    (dominated : ∀ exponent : ℝ, 1 ≤ exponent → ∃ bounds : ℕ → ℝ, Summable bounds ∧
      ∀ step index, (eLpNorm (fields step index) (ENNReal.ofReal exponent) measure).toReal ≤ bounds index)
    (coordinateConverges : ∀ exponent : ℝ, 1 ≤ exponent → ∀ index, Tendsto
      (fun step => eLpNorm (fields step index - limits index) (ENNReal.ofReal exponent) measure) atTop (𝓝 0))
    {lengths : ℕ → ℕ} (truncated : ∀ step index, lengths step ≤ index → fields step index = 0) :
    ∃ limit : Domain → Value, ∀ exponent : ℝ, 1 ≤ exponent →
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun step => eLpNorm ((∑ index ∈ Finset.range (lengths step), fields step index) - limit)
          (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  apply exists_common_limit_of_all_finiteLp_limits
  · intro step
    exact (memLp_finset_sum' (Finset.range (lengths step))
      (fun index _ => members 1 le_rfl step index)).aestronglyMeasurable
  · intro exponent exponentBound
    have lpBound : 1 ≤ ENNReal.ofReal exponent := by
      simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
    letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
    obtain ⟨bounds, summable, bounded⟩ := dominated exponent exponentBound
    exact exists_memLp_limit_of_dominated_triangular_sums
      (members exponent exponentBound) (limitMembers exponent exponentBound) summable bounded
      (coordinateConverges exponent exponentBound) truncated

end MeasureTheory
