import Mathlib

noncomputable section

open MeasureTheory Set

theorem ContinuousOn.integrable_of_isCompact_of_support_subset
    {Domain Value : Type*} [TopologicalSpace Domain] [T2Space Domain]
    [MeasurableSpace Domain] [OpensMeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} [IsFiniteMeasureOnCompacts measure]
    {function : Domain → Value} {compactSet : Set Domain}
    (continuous : ContinuousOn function compactSet) (compact : IsCompact compactSet)
    (supported : Function.support function ⊆ compactSet) : Integrable function measure := by
  have indicatorEquality : compactSet.indicator function = function := by
    funext point
    by_cases inside : point ∈ compactSet
    · exact indicator_of_mem inside function
    · rw [indicator_of_not_mem inside]
      exact (Function.nmem_support.mp (fun inSupport => inside (supported inSupport))).symm
  rw [← indicatorEquality]
  exact (continuous.integrableOn_compact compact).integrable_indicator compact.measurableSet
