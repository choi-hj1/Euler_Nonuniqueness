import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Real.Basic

noncomputable section

namespace EulerNonuniqueness.General

theorem exists_positive_uniform_lower_bound_finite {Index : Type*} [Fintype Index]
    (values : Index → ℝ) (positive : ∀ index, 0 < values index) :
    ∃ margin > 0, ∀ index, margin ≤ values index := by
  classical
  have finiteBound : ∀ indices : Finset Index, ∃ margin > 0,
      ∀ index ∈ indices, margin ≤ values index := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun _ member => False.elim (Finset.not_mem_empty _ member)⟩
    | @insert element indices absent inductionHypothesis =>
      obtain ⟨margin, marginPositive, lowerBound⟩ := inductionHypothesis
      refine ⟨min (values element) margin, lt_min (positive element) marginPositive, ?_⟩
      intro index member
      rcases Finset.mem_insert.mp member with equal | inPrevious
      · subst index
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (lowerBound index inPrevious)
  obtain ⟨margin, marginPositive, lowerBound⟩ := finiteBound Finset.univ
  exact ⟨margin, marginPositive, fun index => lowerBound index (Finset.mem_univ index)⟩

end EulerNonuniqueness.General
