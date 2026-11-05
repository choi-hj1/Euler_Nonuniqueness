import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace EulerNonuniqueness.General

theorem sum_erase_eq_lower_add_adjacent_add_finer
    {Space : Type*} [AddCommMonoid Space] {count : ℕ} (receiver adjacent : Fin count)
    (adjacentIdentity : receiver.val + 1 = adjacent.val) (values : Fin count → Space) :
    (∑ source ∈ Finset.univ.erase receiver, values source) =
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), values source) +
        values adjacent +
        ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val), values source := by
  let lower := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let finer := Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val)
  have partition : Finset.univ.erase receiver = lower ∪ insert adjacent finer := by
    ext source
    simp only [lower, finer, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_union, Finset.mem_insert, Finset.mem_filter, true_and, Fin.ext_iff]
    omega
  have disjoint : Disjoint lower (insert adjacent finer) := by
    apply Finset.disjoint_left.mpr
    intro source lowerMember otherMember
    have below : source.val < receiver.val := (Finset.mem_filter.mp lowerMember).2
    rcases Finset.mem_insert.mp otherMember with same | finerMember
    · subst source
      omega
    · have above : receiver.val + 2 ≤ source.val := (Finset.mem_filter.mp finerMember).2
      omega
  have adjacentAbsent : adjacent ∉ finer := by
    intro member
    have above : receiver.val + 2 ≤ adjacent.val := (Finset.mem_filter.mp member).2
    omega
  rw [partition, Finset.sum_union disjoint, Finset.sum_insert adjacentAbsent]
  exact (add_assoc _ _ _).symm

end EulerNonuniqueness.General
