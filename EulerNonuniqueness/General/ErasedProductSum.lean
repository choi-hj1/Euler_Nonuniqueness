import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Abel

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.General

theorem sum_erase_equiv_prod {Block Part Label Space : Type*}
    [Fintype Block] [DecidableEq Block] [Fintype Part] [DecidableEq Part]
    [Fintype Label] [DecidableEq Label] [AddCommGroup Space]
    (labels : Block × Part ≃ Label) (values : Label → Space) (block : Block) (part : Part) :
    (∑ label ∈ Finset.univ.erase (labels (block, part)), values label) =
      (∑ other ∈ Finset.univ.erase part, values (labels (block, other))) +
        ∑ other ∈ Finset.univ.erase block, ∑ component : Part, values (labels (other, component)) := by
  have total := labels.sum_comp values
  rw [Fintype.sum_prod_type] at total
  have blocks := Finset.sum_erase_add (s := Finset.univ)
    (fun other : Block => ∑ component : Part, values (labels (other, component))) (Finset.mem_univ block)
  have parts := Finset.sum_erase_add (s := Finset.univ)
    (fun other : Part => values (labels (block, other))) (Finset.mem_univ part)
  have entries := Finset.sum_erase_add (s := Finset.univ) values (Finset.mem_univ (labels (block, part)))
  dsimp only at blocks parts
  rw [← blocks, ← parts, ← entries] at total
  exact add_right_cancel (b := values (labels (block, part))) (by rw [← total]; abel)

end EulerNonuniqueness.General
