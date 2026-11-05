import Mathlib

noncomputable section

open Set
open scoped BigOperators

theorem HasCompactSupport.finset_sum
    {Domain Value Index : Type*} [TopologicalSpace Domain] [AddCommMonoid Value]
    {fields : Index → Domain → Value} (indices : Finset Index)
    (compact : ∀ index ∈ indices, HasCompactSupport (fields index)) :
    HasCompactSupport (∑ index ∈ indices, fields index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HasCompactSupport.zero : HasCompactSupport (0 : Domain → Value))
  | @insert index indices outside inductionHypothesis =>
    rw [Finset.sum_insert outside]
    exact (compact index (Finset.mem_insert_self _ _)).add
      (inductionHypothesis (fun other inside => compact other (Finset.mem_insert_of_mem inside)))
