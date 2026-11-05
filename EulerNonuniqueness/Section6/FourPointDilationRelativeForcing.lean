import EulerNonuniqueness.Section6.FourPointDilationDirectional

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointDilationDirectionalRate_norm_le (positions velocity : FourPointConfiguration) :
    |fourPointDilationDirectionalRate positions velocity| ≤ 4 * ‖positions‖ * ‖velocity‖ := by
  have firstPosition := (norm_fst_le (fourPointOddPart positions)).trans (fourPointOddPart_norm_le positions)
  have secondPosition := (norm_snd_le (fourPointOddPart positions)).trans (fourPointOddPart_norm_le positions)
  have firstVelocity := (norm_fst_le (fourPointOddPart velocity)).trans (fourPointOddPart_norm_le velocity)
  have secondVelocity := (norm_snd_le (fourPointOddPart velocity)).trans (fourPointOddPart_norm_le velocity)
  have first := (abs_real_inner_le_norm (fourPointOddPart positions).1 (fourPointOddPart velocity).1).trans
    (mul_le_mul firstPosition firstVelocity (norm_nonneg _) (norm_nonneg _))
  have second := (abs_real_inner_le_norm (fourPointOddPart positions).2 (fourPointOddPart velocity).2).trans
    (mul_le_mul secondPosition secondVelocity (norm_nonneg _) (norm_nonneg _))
  have triangle := abs_sub (2 * @inner ℝ ℂ _ (fourPointOddPart positions).1 (fourPointOddPart velocity).1)
    (2 * @inner ℝ ℂ _ (fourPointOddPart positions).2 (fourPointOddPart velocity).2)
  simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at triangle
  exact triangle.trans ((add_le_add (mul_le_mul_of_nonneg_left first (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left second (by norm_num : (0 : ℝ) ≤ 2))).trans_eq (by ring))

theorem fourPointDilationDirectionalRate_relative_norm_le
    (first second firstVelocity secondVelocity : FourPointConfiguration) :
    |fourPointDilationDirectionalRate first firstVelocity - fourPointDilationDirectionalRate second secondVelocity| ≤
      4 * ‖first - second‖ * ‖secondVelocity‖ + 4 * ‖first‖ * ‖firstVelocity - secondVelocity‖ := by
  have identity : fourPointDilationDirectionalRate first firstVelocity - fourPointDilationDirectionalRate second secondVelocity =
      fourPointDilationDirectionalRate (first - second) secondVelocity +
        fourPointDilationDirectionalRate first (firstVelocity - secondVelocity) := by
    simp only [fourPointDilationDirectionalRate, fourPointOddPart_sub, Prod.fst_sub, Prod.snd_sub,
      inner_sub_left, inner_sub_right]
    ring
  rw [identity]
  exact (abs_add _ _).trans (add_le_add (fourPointDilationDirectionalRate_norm_le _ _)
    (fourPointDilationDirectionalRate_norm_le _ _))

theorem fourPointDilationDirectionalRate_centered
    (positions velocity : FourPointConfiguration) (center : ℂ) :
    fourPointDilationDirectionalRate (fun patch => positions patch - center) velocity =
      fourPointDilationDirectionalRate positions velocity := by
  have odd : fourPointOddPart (fun patch => positions patch - center) = fourPointOddPart positions := by
    ext <;> simp only [fourPointOddPart] <;> congr 1 <;> ring
  simp only [fourPointDilationDirectionalRate, odd]

end EulerNonuniqueness.Section6
