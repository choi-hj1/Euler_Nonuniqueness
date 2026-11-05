import EulerNonuniqueness.Section4.ReferenceStatement

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem quadrupoleCenter_norm_le_of_patchCentroid_norm_le {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) {radius : ℝ}
    (bound : ∀ patch : Fin 4, ‖patchCentroid motion time index patch‖ ≤ radius) :
    ‖quadrupoleCenter motion time index‖ ≤ radius := by
  rw [quadrupoleCenter, norm_div, Complex.norm_ofNat]
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4)) (fun patch => patchCentroid motion time index patch)
  have total := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => bound patch)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  norm_num at total
  linarith only [triangle, total]

end EulerNonuniqueness.Paper
