import EulerNonuniqueness.General.LpSeries

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace MeasureTheory

theorem eLpNorm_toReal_finset_sum_le
    {Domain Value Index : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    {fields : Index → Domain → Value} (members : ∀ index, MemLp (fields index) exponent measure)
    (indices : Finset Index) :
    (eLpNorm (∑ index ∈ indices, fields index) exponent measure).toReal ≤
      ∑ index ∈ indices, (eLpNorm (fields index) exponent measure).toReal := by
  rw [← Lp.norm_toLp _ (memLp_finset_sum' indices (fun index _ => members index)),
    toLp_finset_sum members]
  simpa only [Lp.norm_toLp] using norm_sum_le indices (fun index => (members index).toLp (fields index))

theorem eLpNorm_toReal_sub_le
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    {first second : Domain → Value} (firstMember : MemLp first exponent measure)
    (secondMember : MemLp second exponent measure) :
    (eLpNorm (first - second) exponent measure).toReal ≤
      (eLpNorm first exponent measure).toReal + (eLpNorm second exponent measure).toReal := by
  rw [← Lp.norm_toLp _ (firstMember.sub secondMember), MemLp.toLp_sub]
  simpa only [Lp.norm_toLp] using norm_sub_le (firstMember.toLp first) (secondMember.toLp second)

end MeasureTheory
