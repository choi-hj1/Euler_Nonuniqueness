import EulerNonuniqueness.General.ErasedProductSum

open scoped BigOperators

namespace EulerNonuniqueness.General

theorem sum_erase_filter_equiv_prod {Block Part Label Space : Type*}
    [Fintype Block] [DecidableEq Block] [Fintype Part] [DecidableEq Part]
    [Fintype Label] [DecidableEq Label] [AddCommGroup Space]
    (labels : Block × Part ≃ Label) (values : Label → Space) (block : Block) (part : Part) :
    (∑ label ∈ (Finset.univ.erase (labels (block, part))).filter
      (fun label => (labels.symm label).1 = block), values label) =
      ∑ other ∈ Finset.univ.erase part, values (labels (block, other)) := by
  rw [Finset.sum_filter]
  rw [sum_erase_equiv_prod labels
    (fun label => if (labels.symm label).1 = block then values label else 0) block part]
  simp only [Equiv.symm_apply_apply, if_true]
  have foreignZero : (∑ other ∈ Finset.univ.erase block, ∑ component : Part,
      if other = block then values (labels (other, component)) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro other member
    simp only [if_neg (Finset.mem_erase.mp member).1, Finset.sum_const_zero]
  rw [foreignZero, add_zero]

end EulerNonuniqueness.General
