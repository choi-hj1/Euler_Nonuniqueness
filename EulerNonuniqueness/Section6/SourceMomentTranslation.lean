import EulerNonuniqueness.Section6.PairedStrainRemainder
import EulerNonuniqueness.Section6.PhysicalMomentTargetCoefficient

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem inverse_fourth_power_translation_bound {displacement reference : ℂ}
    (referenceNonzero : reference ≠ 0) (close : ‖displacement - reference‖ ≤ ‖reference‖ / 2) :
    ‖displacement⁻¹ ^ 4 - reference⁻¹ ^ 4‖ ≤ 128 / ‖reference‖ ^ 5 * ‖displacement - reference‖ := by
  have referencePositive : 0 < ‖reference‖ := norm_pos_iff.mpr referenceNonzero
  have lower (position : ℂ) (member : position ∈ Metric.closedBall reference (‖reference‖ / 2)) : ‖reference‖ / 2 ≤ ‖position‖ := by
    have distance : ‖position - reference‖ ≤ ‖reference‖ / 2 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using member
    have triangle : ‖reference‖ ≤ ‖position - reference‖ + ‖position‖ := by
      have actual := norm_add_le (reference - position) position
      rw [sub_add_cancel, norm_sub_rev] at actual
      exact actual
    linarith only [triangle, distance]
  have derivative (position : ℂ) (member : position ∈ Metric.closedBall reference (‖reference‖ / 2)) :
      HasDerivWithinAt (fun current : ℂ => current⁻¹ ^ 4) (-4 / position ^ 5)
        (Metric.closedBall reference (‖reference‖ / 2)) position := by
    have positive : 0 < ‖position‖ := (by positivity : 0 < ‖reference‖ / 2).trans_le (lower position member)
    have nonzero : position ≠ 0 := norm_pos_iff.mp positive
    apply HasDerivAt.hasDerivWithinAt
    convert ((hasDerivAt_id position).inv nonzero).pow 4 using 1 <;> field_simp [nonzero] <;> ring
  have bound (position : ℂ) (member : position ∈ Metric.closedBall reference (‖reference‖ / 2)) :
      ‖-4 / position ^ 5‖ ≤ 128 / ‖reference‖ ^ 5 := by
    simp only [norm_div, norm_pow, norm_neg, Complex.norm_ofNat]
    apply (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
      (pow_pos (by positivity : 0 < ‖reference‖ / 2) 5)
      (pow_le_pow_left₀ (by positivity : 0 ≤ ‖reference‖ / 2) (lower position member) 5)).trans_eq
    field_simp [referencePositive.ne'] <;> ring
  exact (convex_closedBall reference (‖reference‖ / 2)).norm_image_sub_le_of_norm_hasDerivWithin_le derivative bound
    (by simp only [Metric.mem_closedBall, dist_self]; positivity)
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using close)

theorem physical_second_moment_strain_translation_bound (moment : ℂ) {displacement reference : ℂ}
    (referenceNonzero : reference ≠ 0) (close : ‖displacement - reference‖ ≤ ‖reference‖ / 2) :
    ‖(-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / reference ^ 4))‖ ≤
      192 * ‖moment‖ * ‖displacement - reference‖ / (Real.pi * ‖reference‖ ^ 5) := by
  have identity : (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / displacement ^ 4)) -
      (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment / reference ^ 4)) =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * moment) * star (displacement⁻¹ ^ 4 - reference⁻¹ ^ 4) := by
    simp only [div_eq_mul_inv, inv_pow, star_mul, star_sub]
    ring
  rw [identity, norm_mul, norm_mul, norm_star, norm_star, norm_mul]
  have estimate := mul_le_mul_of_nonneg_left (inverse_fourth_power_translation_bound referenceNonzero close)
    (show 0 ≤ ‖-(Complex.I / ((2 * Real.pi : ℝ) : ℂ))‖ * (‖(3 : ℂ)‖ * ‖moment‖) by positivity)
  apply estimate.trans_eq
  simp only [norm_neg, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), Complex.norm_ofNat]
  ring

end EulerNonuniqueness.Section6
