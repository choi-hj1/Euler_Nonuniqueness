import EulerNonuniqueness.General.LpSeries

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

namespace MeasureTheory

theorem exists_memLp_limit_of_dominated_triangular_sums
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value] [CompleteSpace Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)]
    {fields : ℕ → ℕ → Domain → Value} {limits : ℕ → Domain → Value}
    (members : ∀ step index, MemLp (fields step index) exponent measure)
    (limitMembers : ∀ index, MemLp (limits index) exponent measure)
    {bounds : ℕ → ℝ} (summable : Summable bounds)
    (bounded : ∀ step index, (eLpNorm (fields step index) exponent measure).toReal ≤ bounds index)
    (coordinateConverges : ∀ index, Tendsto
      (fun step => eLpNorm (fields step index - limits index) exponent measure) atTop (𝓝 0))
    {lengths : ℕ → ℕ} (truncated : ∀ step index, lengths step ≤ index → fields step index = 0) :
    ∃ limit : Domain → Value, MemLp limit exponent measure ∧ Tendsto
      (fun step => eLpNorm ((∑ index ∈ Finset.range (lengths step), fields step index) - limit)
        exponent measure) atTop (𝓝 0) := by
  let elements : ℕ → ℕ → Lp Value exponent measure :=
    fun step index => (members step index).toLp (fields step index)
  let limitElements : ℕ → Lp Value exponent measure :=
    fun index => (limitMembers index).toLp (limits index)
  have quotientCoordinates (index : ℕ) : Tendsto (fun step => elements step index) atTop
      (𝓝 (limitElements index)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun step => members step index) _ (limitMembers index)).mpr
      (coordinateConverges index)
  have quotientBounds (step index : ℕ) : ‖elements step index‖ ≤ bounds index := by
    simpa only [elements, Lp.norm_toLp] using bounded step index
  have seriesConverges := tendsto_tsum_of_dominated_convergence summable quotientCoordinates
    (Eventually.of_forall quotientBounds)
  let limitElement := ∑' index, limitElements index
  have limitMember : MemLp (limitElement : Domain → Value) exponent measure := Lp.memLp limitElement
  have sumEquality (step : ℕ) :
      (memLp_finset_sum' (Finset.range (lengths step)) (fun index _ => members step index)).toLp
        (∑ index ∈ Finset.range (lengths step), fields step index) = ∑' index, elements step index := by
    rw [toLp_finset_sum]
    symm
    apply tsum_eq_sum
    intro index outside
    have large : lengths step ≤ index := Nat.le_of_not_gt (fun less => outside (Finset.mem_range.mpr less))
    simp only [elements, truncated step index large, MemLp.toLp_zero]
  have quotientConverges : Tendsto
      (fun step => (memLp_finset_sum' (Finset.range (lengths step)) (fun index _ => members step index)).toLp
        (∑ index ∈ Finset.range (lengths step), fields step index)) atTop
      (𝓝 (limitMember.toLp (limitElement : Domain → Value))) := by
    simpa only [sumEquality, Lp.toLp_coeFn] using seriesConverges
  exact ⟨limitElement, limitMember,
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).mp quotientConverges⟩

end MeasureTheory
