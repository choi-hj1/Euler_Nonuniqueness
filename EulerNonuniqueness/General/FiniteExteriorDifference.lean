import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.General

theorem norm_sum_erase_sub_sum_erase_le {Index Space : Type*} [Fintype Index] [DecidableEq Index]
    [NormedAddCommGroup Space] (first second : Index) (different : first ≠ second)
    (firstValues secondValues : Index → Space) :
    ‖(∑ source ∈ Finset.univ.erase first, firstValues source) -
      (∑ source ∈ Finset.univ.erase second, secondValues source)‖ ≤
      (∑ source ∈ (Finset.univ.erase first).erase second,
        ‖firstValues source - secondValues source‖) + ‖firstValues second‖ + ‖secondValues first‖ := by
  have firstIdentity := Finset.sum_erase_add (s := Finset.univ.erase first) firstValues
    (Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ second⟩)
  have secondIdentity := Finset.sum_erase_add (s := Finset.univ.erase second) secondValues
    (Finset.mem_erase.mpr ⟨different, Finset.mem_univ first⟩)
  have eraseEquality : (Finset.univ.erase second).erase first = (Finset.univ.erase first).erase second := by
    ext source
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  rw [← firstIdentity, ← secondIdentity, eraseEquality]
  have identity :
      ((∑ source ∈ (Finset.univ.erase first).erase second, firstValues source) + firstValues second) -
        ((∑ source ∈ (Finset.univ.erase first).erase second, secondValues source) + secondValues first) =
      (∑ source ∈ (Finset.univ.erase first).erase second, (firstValues source - secondValues source)) +
        (firstValues second - secondValues first) := by
    rw [Finset.sum_sub_distrib]
    abel
  rw [identity]
  exact (norm_add_le _ _).trans ((add_le_add (norm_sum_le _ _) (norm_sub_le _ _)).trans_eq (by ring))

end EulerNonuniqueness.General
