import EulerNonuniqueness.Section1.Scales

noncomputable section

namespace EulerNonuniqueness.Paper

theorem Scales.location_eq_half_pow (scales : Scales) (index : ℕ) :
    scales.location index = (1 / 2 : ℝ) ^ index := by
  simp only [scales.location_eq_inv_pow, one_div, inv_pow]

theorem Scales.location_antitone (scales : Scales) : Antitone scales.location := by
  intro first second ordered
  simp_rw [scales.location_eq_half_pow]
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) ordered

theorem Scales.location_le_half_of_lt (scales : Scales) {first second : ℕ} (ordered : first < second) :
    scales.location second ≤ scales.location first / 2 := by
  have estimate := scales.location_antitone (Nat.succ_le_of_lt ordered)
  simpa only [scales.location_eq_half_pow, pow_succ, div_eq_mul_inv, one_mul] using estimate

theorem Scales.location_sum_le_three_distance (scales : Scales) {first second : ℕ} (different : first ≠ second) :
    scales.location first + scales.location second ≤
      3 * |scales.location first - scales.location second| := by
  rcases lt_or_gt_of_ne different with ordered | ordered
  · have estimate := scales.location_le_half_of_lt ordered
    have nonnegative := (scales.location_pos second).le
    rw [abs_of_nonneg (by linarith : 0 ≤ scales.location first - scales.location second)]
    linarith
  · have estimate := scales.location_le_half_of_lt ordered
    have nonnegative := (scales.location_pos first).le
    rw [abs_of_nonpos (by linarith : scales.location first - scales.location second ≤ 0)]
    linarith

theorem Scales.location_distance_pos (scales : Scales) {first second : ℕ} (different : first ≠ second) :
    0 < |scales.location first - scales.location second| := by
  have bound := scales.location_sum_le_three_distance different
  linarith [scales.location_pos first, scales.location_pos second]

end EulerNonuniqueness.Paper
