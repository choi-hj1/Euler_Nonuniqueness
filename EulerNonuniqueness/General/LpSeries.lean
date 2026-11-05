import Mathlib

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace MeasureTheory

theorem toLp_finset_sum {Domain Value Index : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Value] {measure : Measure Domain} {exponent : ℝ≥0∞}
    [Fact (1 ≤ exponent)] {fields : Index → Domain → Value}
    (members : ∀ index, MemLp (fields index) exponent measure) (indices : Finset Index) :
    (memLp_finset_sum' indices (fun index _ => members index)).toLp (∑ index ∈ indices, fields index) =
      ∑ index ∈ indices, (members index).toLp (fields index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices outside inductionHypothesis =>
    simp only [Finset.sum_insert outside]
    rw [MemLp.toLp_add, inductionHypothesis]

theorem exists_memLp_limit_of_summable_eLpNorm
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value] [CompleteSpace Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    {fields : ℕ → Domain → Value} (members : ∀ index, MemLp (fields index) exponent measure)
    (summable : Summable (fun index => (eLpNorm (fields index) exponent measure).toReal)) :
    ∃ limit : Domain → Value, MemLp limit exponent measure ∧ Tendsto
      (fun count => eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit) exponent measure)
      atTop (𝓝 0) := by
  let elements : ℕ → Lp Value exponent measure := fun index => (members index).toLp (fields index)
  have normsSummable : Summable (fun index => ‖elements index‖) := by
    simpa only [elements, Lp.norm_toLp] using summable
  have elementsSummable : Summable elements := normsSummable.of_norm
  let limit := ∑' index, elements index
  have limitMember : MemLp (limit : Domain → Value) exponent measure := Lp.memLp limit
  have quotientConverges : Tendsto
      (fun count => (memLp_finset_sum' (Finset.range count) (fun index _ => members index)).toLp
        (∑ index ∈ Finset.range count, fields index)) atTop (𝓝 (limitMember.toLp (limit : Domain → Value))) := by
    have sumsEqual : (fun count =>
        (memLp_finset_sum' (Finset.range count) (fun index _ => members index)).toLp
          (∑ index ∈ Finset.range count, fields index)) =
        (fun count => ∑ index ∈ Finset.range count, elements index) := by
      funext count
      exact toLp_finset_sum members (Finset.range count)
    rw [sumsEqual, Lp.toLp_coeFn]
    exact elementsSummable.hasSum.tendsto_sum_nat
  exact ⟨limit, limitMember,
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mp quotientConverges⟩

theorem ae_eq_of_tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {sequence : ℕ → Domain → Value} {first second : Domain → Value}
    {firstExponent secondExponent : ℝ≥0∞} (firstNonzero : firstExponent ≠ 0)
    (secondNonzero : secondExponent ≠ 0)
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    (firstMeasurable : AEStronglyMeasurable first measure)
    (secondMeasurable : AEStronglyMeasurable second measure)
    (firstConverges : Tendsto (fun index => eLpNorm (sequence index - first) firstExponent measure) atTop (𝓝 0))
    (secondConverges : Tendsto (fun index => eLpNorm (sequence index - second) secondExponent measure) atTop (𝓝 0)) :
    first =ᵐ[measure] second :=
  tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm firstNonzero measurable firstMeasurable firstConverges)
    (tendstoInMeasure_of_tendsto_eLpNorm secondNonzero measurable secondMeasurable secondConverges)

theorem exists_all_finiteLp_limit_of_summable_eLpNorm
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value] [CompleteSpace Value]
    {measure : Measure Domain} {fields : ℕ → Domain → Value}
    (members : ∀ exponent : ℝ, 1 ≤ exponent → ∀ index,
      MemLp (fields index) (ENNReal.ofReal exponent) measure)
    (summable : ∀ exponent : ℝ, 1 ≤ exponent →
      Summable (fun index => (eLpNorm (fields index) (ENNReal.ofReal exponent) measure).toReal)) :
    ∃ limit : Domain → Value, ∀ exponent : ℝ, 1 ≤ exponent →
      MemLp limit (ENNReal.ofReal exponent) measure ∧ Tendsto
        (fun count => eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit)
          (ENNReal.ofReal exponent) measure) atTop (𝓝 0) := by
  have oneMembers : ∀ index, MemLp (fields index) 1 measure := by
    simpa only [ENNReal.ofReal_one] using members 1 le_rfl
  have oneSummable : Summable (fun index => (eLpNorm (fields index) 1 measure).toReal) := by
    simpa only [ENNReal.ofReal_one] using summable 1 le_rfl
  obtain ⟨limit, limitMember, oneConverges⟩ :=
    exists_memLp_limit_of_summable_eLpNorm oneMembers oneSummable
  refine ⟨limit, fun exponent exponentBound => ?_⟩
  have lpBound : 1 ≤ ENNReal.ofReal exponent := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal exponentBound
  letI : Fact (1 ≤ ENNReal.ofReal exponent) := ⟨lpBound⟩
  obtain ⟨candidate, candidateMember, candidateConverges⟩ :=
    exists_memLp_limit_of_summable_eLpNorm (members exponent exponentBound) (summable exponent exponentBound)
  have equal : candidate =ᵐ[measure] limit :=
    ae_eq_of_tendsto_eLpNorm_sub_of_tendsto_eLpNorm_sub
      (ne_of_gt (zero_lt_one.trans_le lpBound)) (by norm_num)
      (fun count => (memLp_finset_sum' (Finset.range count)
        (fun index _ => oneMembers index)).aestronglyMeasurable)
      candidateMember.aestronglyMeasurable limitMember.aestronglyMeasurable
      candidateConverges oneConverges
  refine ⟨(memLp_congr_ae equal).mp candidateMember, ?_⟩
  have normEqual (count : ℕ) :
      eLpNorm ((∑ index ∈ Finset.range count, fields index) - candidate) (ENNReal.ofReal exponent) measure =
      eLpNorm ((∑ index ∈ Finset.range count, fields index) - limit) (ENNReal.ofReal exponent) measure := by
    apply eLpNorm_congr_ae
    filter_upwards [equal] with point equality
    simp only [Pi.sub_apply, equality]
  simpa only [normEqual] using candidateConverges

end MeasureTheory
