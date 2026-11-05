import EulerNonuniqueness.Section6.FourPointCenterProjection

noncomputable section

open Set
open scoped NNReal BigOperators

namespace EulerNonuniqueness.Section6

theorem fourPointCenterProjection_norm_le_pairwise (velocity : FourPointConfiguration) {bound : ℝ}
    (nonnegative : 0 ≤ bound) (pairwise : ∀ first second, ‖velocity first - velocity second‖ ≤ bound) :
    ‖fourPointCenterProjection velocity‖ ≤ bound := by
  apply (pi_norm_le_iff_of_nonneg nonnegative).mpr
  intro target
  have identity : fourPointCenterProjection velocity target =
      (∑ source : Fin 4, (velocity target - velocity source)) / 4 := by
    simp only [fourPointCenterProjection, fourPointArithmeticCenter, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    ring
  rw [identity, norm_div, Complex.norm_ofNat]
  have triangle := norm_sum_le (Finset.univ : Finset (Fin 4)) (fun source => velocity target - velocity source)
  have total := Finset.sum_le_sum (fun source (_ : source ∈ (Finset.univ : Finset (Fin 4))) => pairwise target source)
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at total
  norm_num only [Nat.cast_ofNat] at total
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr (by linarith)

theorem fourPointCenterProjection_external_norm_le {positions : FourPointConfiguration}
    {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0} {extent : ℝ}
    (externalLipschitz : LipschitzOnWith strain external region)
    (inside : ∀ patch, positions patch ∈ region)
    (bounded : ∀ patch, ‖positions patch - fourPointArithmeticCenter positions‖ ≤ extent) :
    ‖fourPointCenterProjection (fun patch => external (positions patch))‖ ≤ 2 * (strain : ℝ) * extent := by
  have extentNonnegative : 0 ≤ extent := (norm_nonneg _).trans (bounded 0)
  apply fourPointCenterProjection_norm_le_pairwise _ (by positivity)
  intro patch source
  have lipschitz := externalLipschitz.norm_sub_le (inside patch) (inside source)
  have triangle := norm_sub_le_norm_sub_add_norm_sub (positions patch)
    (fourPointArithmeticCenter positions) (positions source)
  rw [norm_sub_rev (fourPointArithmeticCenter positions) (positions source)] at triangle
  have distance : ‖positions patch - positions source‖ ≤ 2 * extent := by linarith [bounded patch, bounded source]
  exact lipschitz.trans ((mul_le_mul_of_nonneg_left distance strain.coe_nonneg).trans_eq (by ring))

end EulerNonuniqueness.Section6
