import EulerNonuniqueness.Section6.FourPointShapeReduction

noncomputable section

namespace EulerNonuniqueness.Section6

theorem point_velocity_radial_balance (coefficient : ℝ) {positive negative : ℂ}
    (positiveNonzero : positive ≠ 0) (negativeNonzero : negative ≠ 0)
    (squaresNonzero : star positive ^ 2 - star negative ^ 2 ≠ 0) (normOrder : ‖negative‖ < ‖positive‖) :
    2 * @inner ℝ ℂ _ positive (positivePointVelocity coefficient positive negative) -
      2 * @inner ℝ ℂ _ negative (negativePointVelocity coefficient positive negative) = 0 := by
  let positivePath : ℝ → ℂ := fun time => positive + time • positivePointVelocity coefficient positive negative
  let negativePath : ℝ → ℂ := fun time => negative + time • negativePointVelocity coefficient positive negative
  have positiveDerivative : HasDerivAt positivePath (positivePointVelocity coefficient positive negative) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (positivePointVelocity coefficient positive negative)).const_add positive
  have negativeDerivative : HasDerivAt negativePath (negativePointVelocity coefficient positive negative) 0 := by
    simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const
      (negativePointVelocity coefficient positive negative)).const_add negative
  have positiveAtZero : positivePath 0 = positive := by simp [positivePath]
  have negativeAtZero : negativePath 0 = negative := by simp [negativePath]
  have central := four_point_impulse_hasDerivAt coefficient
    (positiveAtZero.symm ▸ positiveNonzero) (negativeAtZero.symm ▸ negativeNonzero)
    (by simpa only [positiveAtZero, negativeAtZero] using squaresNonzero)
    (by simpa only [positiveAtZero, negativeAtZero] using normOrder)
    (by simpa only [positiveAtZero, negativeAtZero] using positiveDerivative)
    (by simpa only [positiveAtZero, negativeAtZero] using negativeDerivative)
  have direct := positiveDerivative.norm_sq.sub negativeDerivative.norm_sq
  simpa only [positiveAtZero, negativeAtZero] using (direct.unique central)

theorem forced_point_impulse_hasDerivAt (coefficient : ℝ) {positive negative : ℝ → ℂ}
    {positiveForcing negativeForcing : ℂ} {time : ℝ}
    (positiveNonzero : positive time ≠ 0) (negativeNonzero : negative time ≠ 0)
    (squaresNonzero : star (positive time) ^ 2 - star (negative time) ^ 2 ≠ 0)
    (normOrder : ‖negative time‖ < ‖positive time‖)
    (positiveDerivative : HasDerivAt positive
      (positivePointVelocity coefficient (positive time) (negative time) + positiveForcing) time)
    (negativeDerivative : HasDerivAt negative
      (negativePointVelocity coefficient (positive time) (negative time) + negativeForcing) time) :
    HasDerivAt (fun current => ‖positive current‖ ^ 2 - ‖negative current‖ ^ 2)
      (2 * @inner ℝ ℂ _ (positive time) positiveForcing -
        2 * @inner ℝ ℂ _ (negative time) negativeForcing) time := by
  have balance := point_velocity_radial_balance coefficient positiveNonzero negativeNonzero squaresNonzero normOrder
  convert positiveDerivative.norm_sq.sub negativeDerivative.norm_sq using 1
  simp only [inner_add_right]
  linarith

theorem forced_point_impulse_rate_bound (positive negative positiveForcing negativeForcing : ℂ) :
    |2 * @inner ℝ ℂ _ positive positiveForcing - 2 * @inner ℝ ℂ _ negative negativeForcing| ≤
      2 * (‖positive‖ + ‖negative‖) * ‖(positiveForcing, negativeForcing)‖ := by
  calc
    _ ≤ |2 * @inner ℝ ℂ _ positive positiveForcing| + |2 * @inner ℝ ℂ _ negative negativeForcing| := abs_sub _ _
    _ = 2 * |@inner ℝ ℂ _ positive positiveForcing| + 2 * |@inner ℝ ℂ _ negative negativeForcing| := by
      rw [abs_mul, abs_mul]
      norm_num
    _ ≤ 2 * (‖positive‖ * ‖positiveForcing‖) + 2 * (‖negative‖ * ‖negativeForcing‖) := by
      gcongr
      · exact abs_real_inner_le_norm _ _
      · exact abs_real_inner_le_norm _ _
    _ ≤ 2 * (‖positive‖ * ‖(positiveForcing, negativeForcing)‖) +
        2 * (‖negative‖ * ‖(positiveForcing, negativeForcing)‖) := by
      gcongr
      · exact norm_fst_le (positiveForcing, negativeForcing)
      · exact norm_snd_le (positiveForcing, negativeForcing)
    _ = _ := by ring

end EulerNonuniqueness.Section6
