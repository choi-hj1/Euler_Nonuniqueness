import EulerNonuniqueness.Section1.IndividualPatchInteractionWeight

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Paper

theorem Scales.sum_fourPatchInteractionWeight_eq {count : ℕ} (scales : Scales) (receiver : Fin count) :
    (∑ source : Fin (count * 4),
      scales.circulation ((finProdFinEquiv.symm source).1.val + 1) /
        scales.individualInteractionDistance (receiver.val + 1) ((finProdFinEquiv.symm source).1.val + 1) ^ 2) =
      4 * ∑ source : Fin count, scales.circulation (source.val + 1) /
        scales.individualInteractionDistance (receiver.val + 1) (source.val + 1) ^ 2 := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  norm_num

theorem Scales.sum_fourPatchInteractionWeight_le {count : ℕ} (scales : Scales)
    (frequencyBound : 1 ≤ scales.frequency) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (receiver : Fin count) :
    (∑ source : Fin (count * 4),
      scales.circulation ((finProdFinEquiv.symm source).1.val + 1) /
        scales.individualInteractionDistance (receiver.val + 1) ((finProdFinEquiv.symm source).1.val + 1) ^ 2) ≤
      80000 * Real.pi * scales.omega (receiver.val + 1) + 2304 * scales.strain := by
  rw [scales.sum_fourPatchInteractionWeight_eq]
  have estimate := mul_le_mul_of_nonneg_left
    (scales.sum_individualInteractionWeight_le frequencyBound ratioBound alphaPositive receiver) (by norm_num : (0 : ℝ) ≤ 4)
  nlinarith

end EulerNonuniqueness.Paper
