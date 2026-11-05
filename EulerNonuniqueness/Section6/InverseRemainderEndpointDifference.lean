import EulerNonuniqueness.Section6.CenteredDomainInversePowerCorrection

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000

theorem conjugateInverseTaylorRemainder_eq_quadratic {displacement position : ℂ}
    (nonzero : displacement ≠ 0) (gap : displacement - position ≠ 0) :
    conjugateInversePowerTaylorRemainder displacement 0 position =
      star position ^ 2 * (star displacement)⁻¹ ^ 2 * (star (displacement - position))⁻¹ := by
  have conjugateNonzero := star_ne_zero.mpr nonzero
  have conjugateGap := star_ne_zero.mpr gap
  have identity (base increment : ℂ) (baseNonzero : base ≠ 0)
      (differenceNonzero : base - increment ≠ 0) :
      (base - increment)⁻¹ - base⁻¹ - base⁻¹ ^ 2 * increment =
        increment ^ 2 * base⁻¹ ^ 2 * (base - increment)⁻¹ := by
    field_simp [baseNonzero, differenceNonzero]
    <;> ring
  simpa only [conjugateInversePowerTaylorRemainder, Nat.cast_zero, zero_add,
    Nat.reduceAdd, pow_one, one_mul, star_sub] using
    identity (star displacement) (star position) conjugateNonzero (by simpa only [star_sub] using conjugateGap)

theorem conjugateInverseTaylorRemainder_endpoint_difference_bound
    (first second position : ℂ) {distance : ℝ} (positive : 0 < distance)
    (firstSeparated : distance ≤ ‖first‖) (secondSeparated : distance ≤ ‖second‖)
    (firstGap : distance ≤ ‖first - position‖) (secondGap : distance ≤ ‖second - position‖) :
    ‖conjugateInversePowerTaylorRemainder first 0 position -
      conjugateInversePowerTaylorRemainder second 0 position‖ ≤
        3 * distance⁻¹ ^ 4 * ‖position‖ ^ 2 * ‖first - second‖ := by
  rw [conjugateInverseTaylorRemainder_eq_quadratic
      (norm_pos_iff.mp (positive.trans_le firstSeparated)) (norm_pos_iff.mp (positive.trans_le firstGap)),
    conjugateInverseTaylorRemainder_eq_quadratic
      (norm_pos_iff.mp (positive.trans_le secondSeparated)) (norm_pos_iff.mp (positive.trans_le secondGap))]
  have identity : star position ^ 2 * (star first)⁻¹ ^ 2 * (star (first - position))⁻¹ -
      star position ^ 2 * (star second)⁻¹ ^ 2 * (star (second - position))⁻¹ =
    star position ^ 2 * ((star first)⁻¹ ^ 2 - (star second)⁻¹ ^ 2) * (star (first - position))⁻¹ +
      star position ^ 2 * (star second)⁻¹ ^ 2 *
        ((star (first - position))⁻¹ - (star (second - position))⁻¹) := by ring
  rw [identity]
  have squareDifference := conjugate_inverse_power_difference_bound positive firstSeparated secondSeparated 1
  have inverseDifference := conjugate_inverse_power_difference_bound positive firstGap secondGap 0
  simp only [Nat.cast_one, Nat.cast_zero, zero_add, Nat.reduceAdd, one_mul,
    pow_one, sub_sub_sub_cancel_right] at squareDifference inverseDifference
  rw [show (1 + 1 : ℝ) = 2 by norm_num] at squareDifference
  have firstInverse : ‖(star (first - position))⁻¹‖ ≤ distance⁻¹ := by
    simpa only [norm_inv, norm_star] using inv_anti₀ positive firstGap
  have secondSquare : ‖(star second)⁻¹ ^ 2‖ ≤ distance⁻¹ ^ 2 := by
    rw [norm_pow, norm_inv, norm_star]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ positive secondSeparated) 2
  have firstTerm :
      ‖star position ^ 2 * ((star first)⁻¹ ^ 2 - (star second)⁻¹ ^ 2) * (star (first - position))⁻¹‖ ≤
        ‖position‖ ^ 2 * (2 * distance⁻¹ ^ 3 * ‖first - second‖) * distance⁻¹ := by
    rw [norm_mul, norm_mul, norm_pow, norm_star]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left squareDifference (sq_nonneg ‖position‖)) firstInverse
      (norm_nonneg _) (by positivity)
  have secondTerm :
      ‖star position ^ 2 * (star second)⁻¹ ^ 2 *
        ((star (first - position))⁻¹ - (star (second - position))⁻¹)‖ ≤
        ‖position‖ ^ 2 * distance⁻¹ ^ 2 * (distance⁻¹ ^ 2 * ‖first - second‖) := by
    rw [norm_mul, norm_mul, norm_pow, norm_star]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_left secondSquare (sq_nonneg ‖position‖)) inverseDifference
      (norm_nonneg _) (by positivity)
  exact (norm_add_le _ _).trans ((add_le_add firstTerm secondTerm).trans_eq (by ring))

theorem centeredDomainInverseCorrection_endpoint_difference_norm_le {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (center first second : ℂ) {radius distance : ℝ} (radiusNonnegative : 0 ≤ radius)
    (positive : 0 < distance) (bounded : ∀ source ∈ domain, ‖source - center‖ ≤ radius)
    (firstSeparated : radius + distance ≤ ‖first - center‖)
    (secondSeparated : radius + distance ≤ ‖second - center‖)
    (centered : (∫ source in domain, source - center) = 0) :
    ‖centeredDomainInversePowerCorrection domain center first 0 -
      centeredDomainInversePowerCorrection domain center second 0‖ ≤
        volume.real domain * (3 * distance⁻¹ ^ 4 * radius ^ 2) * ‖first - second‖ := by
  have sourceGap (receiver : ℂ) (separated : radius + distance ≤ ‖receiver - center‖)
      (source : ℂ) (member : source ∈ domain) : distance ≤ ‖receiver - source‖ := by
    have triangle := norm_add_le (receiver - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith [bounded source member]
  rw [centeredDomainInversePowerCorrection_eq_integral_remainder measurable finite center first 0 positive
      bounded firstSeparated centered,
    centeredDomainInversePowerCorrection_eq_integral_remainder measurable finite center second 0 positive
      bounded secondSeparated centered,
    ← integral_sub
      (integrableOn_conjugate_inverse_power_taylor_remainder measurable finite center first 0 positive bounded firstSeparated)
      (integrableOn_conjugate_inverse_power_taylor_remainder measurable finite center second 0 positive bounded secondSeparated)]
  have actual := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (show Integrable (fun _ : ℂ => 3 * distance⁻¹ ^ 4 * radius ^ 2 * ‖first - second‖)
      (volume.restrict domain) from integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      have estimate := conjugateInverseTaylorRemainder_endpoint_difference_bound
        (first - center) (second - center) (source - center) positive
        (by linarith) (by linarith)
        (by simpa only [sub_sub_sub_cancel_right] using sourceGap first firstSeparated source member)
        (by simpa only [sub_sub_sub_cancel_right] using sourceGap second secondSeparated source member)
      simp only [sub_sub_sub_cancel_right] at estimate
      apply estimate.trans
      have squareBound := pow_le_pow_left₀ (norm_nonneg (source - center)) (bounded source member) 2
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left squareBound (by positivity : 0 ≤ 3 * distance⁻¹ ^ 4))
        (norm_nonneg (first - second)))
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_assoc] using actual

end EulerNonuniqueness.Section6
