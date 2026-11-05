import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.General

theorem norm_four_average_sub_le (values : Fin 4 → ℂ) (anchor : ℂ) {bound : ℝ}
    (bounded : ∀ source, ‖values source - anchor‖ ≤ bound) :
    ‖(∑ source : Fin 4, values source) / 4 - anchor‖ ≤ bound := by
  have identity : (∑ source : Fin 4, values source) / 4 - anchor =
      (∑ source : Fin 4, (values source - anchor)) / 4 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    push_cast
    ring
  rw [identity, norm_div, Complex.norm_ofNat]
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4)) (fun source => values source - anchor)
  have total := Finset.sum_le_sum (fun source (_ : source ∈ (Finset.univ : Finset (Fin 4))) => bounded source)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  norm_num only [Nat.cast_ofNat] at total
  linarith

end EulerNonuniqueness.General
