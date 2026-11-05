import EulerNonuniqueness.Section6.FourPointTranslationControl

noncomputable section

open scoped BigOperators

namespace EulerNonuniqueness.Section6

def fourPointExternalTaylorRemainder (field : ℂ → ℂ) (center : ℂ)
    (linear : ℂ →L[ℝ] ℂ) (positions : FourPointConfiguration) : FourPointConfiguration :=
  fun target => field (positions target) - field center - linear (positions target - center)

theorem fourPointSignedMoment_external_taylor (field : ℂ → ℂ) (center : ℂ)
    (linear : ℂ →L[ℝ] ℂ) (positions : FourPointConfiguration) :
    fourPointSignedMoment (fun target => field (positions target)) =
      linear (fourPointSignedMoment positions) +
        fourPointSignedMoment (fourPointExternalTaylorRemainder field center linear positions) := by
  simp [fourPointSignedMoment, fourPointSign, Fin.sum_univ_succ, fourPointExternalTaylorRemainder,
    map_add, map_sub]
  abel

theorem fourPointExternalTaylorRemainder_uniform_bound {field : ℂ → ℂ} {base : ℂ}
    (smooth : ContDiffAt ℝ 2 field base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ center : ℂ, ∀ positions : FourPointConfiguration,
      ‖center - base‖ < radius → ‖positions - fun _ => center‖ < radius →
      ‖fourPointExternalTaylorRemainder field center (fderiv ℝ field center) positions‖ ≤
        bound * ‖positions - fun _ => center‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    contDiffAt_uniform_quadratic_remainder smooth
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro center positions centerSmall positionsSmall
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg boundNonnegative (sq_nonneg _))).mpr
  intro target
  have pointNorm : ‖positions target - center‖ ≤ ‖positions - fun _ => center‖ :=
    norm_le_pi_norm (positions - fun _ => center) target
  have control := estimate center (positions target - center) centerSmall (pointNorm.trans_lt positionsSmall)
  have identity : center + (positions target - center) = positions target := by abel
  rw [identity] at control
  exact control.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) pointNorm 2) boundNonnegative)

theorem fourPointSignedMoment_external_bound {field : ℂ → ℂ} {base : ℂ}
    (smooth : ContDiffAt ℝ 2 field base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ center : ℂ, ∀ positions : FourPointConfiguration,
      ‖center - base‖ < radius → ‖positions - fun _ => center‖ < radius →
      ‖fourPointSignedMoment (fun target => field (positions target))‖ ≤
        ‖fderiv ℝ field center‖ * ‖fourPointSignedMoment positions‖ +
          4 * bound * ‖positions - fun _ => center‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointExternalTaylorRemainder_uniform_bound smooth
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro center positions centerSmall positionsSmall
  rw [fourPointSignedMoment_external_taylor field center (fderiv ℝ field center) positions]
  apply (norm_add_le _ _).trans
  apply add_le_add ((fderiv ℝ field center).le_opNorm _)
  exact (fourPointSignedMoment_norm_le _).trans (by
    have control := estimate center positions centerSmall positionsSmall
    nlinarith)

theorem fourPointArithmeticCenter_external_taylor (field : ℂ → ℂ)
    (linear : ℂ →L[ℝ] ℂ) (positions : FourPointConfiguration) :
    fourPointArithmeticCenter (fun target => field (positions target)) =
      field (fourPointArithmeticCenter positions) +
        fourPointArithmeticCenter
          (fourPointExternalTaylorRemainder field (fourPointArithmeticCenter positions) linear positions) := by
  have sumDisplacement : (∑ target : Fin 4, (positions target - fourPointArithmeticCenter positions)) = 0 := by
    simp [fourPointArithmeticCenter, Fin.sum_univ_succ]
    ring
  have sumLinear : (∑ target : Fin 4, linear (positions target - fourPointArithmeticCenter positions)) = 0 := by
    rw [← map_sum, sumDisplacement, map_zero]
  simp only [fourPointArithmeticCenter, fourPointExternalTaylorRemainder, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at sumLinear ⊢
  rw [sumLinear]
  ring

theorem fourPointArithmeticCenter_external_bound {field : ℂ → ℂ} {base : ℂ}
    (smooth : ContDiffAt ℝ 2 field base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ positions : FourPointConfiguration,
      ‖fourPointArithmeticCenter positions - base‖ < radius →
      ‖positions - fun _ => fourPointArithmeticCenter positions‖ < radius →
      ‖fourPointArithmeticCenter (fun target => field (positions target)) -
        field (fourPointArithmeticCenter positions)‖ ≤
        bound * ‖positions - fun _ => fourPointArithmeticCenter positions‖ ^ 2 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointExternalTaylorRemainder_uniform_bound smooth
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro positions centerSmall positionsSmall
  rw [fourPointArithmeticCenter_external_taylor field (fderiv ℝ field (fourPointArithmeticCenter positions)) positions,
    add_sub_cancel_left]
  exact (fourPointArithmeticCenter_norm_le _).trans
    (estimate (fourPointArithmeticCenter positions) positions centerSmall positionsSmall)

end EulerNonuniqueness.Section6
