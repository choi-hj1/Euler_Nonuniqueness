import EulerNonuniqueness.Section6.InversePowerTaylorRelative

noncomputable section

open Metric

namespace EulerNonuniqueness.Section6

theorem conjugateInversePowerTaylorRemainder_receiver_hasFDerivAt
    (displacement position : ℂ) (power : ℕ)
    (displacementNonzero : displacement ≠ 0) (sourceNonzero : displacement - position ≠ 0) :
    HasFDerivAt (fun current => conjugateInversePowerTaylorRemainder current power position)
      ((-(power + 1 : ℂ) * conjugateInversePowerTaylorRemainder displacement (power + 1) position) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) displacement := by
  have source := (conjugateInversePower_hasFDerivAt sourceNonzero power).comp displacement
    ((hasFDerivAt_id (𝕜 := ℝ) displacement).sub_const position)
  have base := conjugateInversePower_hasFDerivAt displacementNonzero power
  have linear := ((conjugateInversePower_hasFDerivAt displacementNonzero (power + 1)).const_mul
    (power + 1 : ℂ)).mul_const (star position)
  convert (source.sub base).sub linear using 1
  apply ContinuousLinearMap.ext
  intro direction
  simp only [conjugateInversePowerTaylorRemainder, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, starRingEnd_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Nat.cast_add, Nat.cast_one,
    Nat.add_assoc, Nat.reduceAdd]
  ring

theorem conjugateInversePowerTaylorRemainder_norm_le (displacement position : ℂ) (power : ℕ)
    {radius distance : ℝ} (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖) (positionBound : ‖position‖ ≤ radius) :
    ‖conjugateInversePowerTaylorRemainder displacement power position‖ ≤
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) * ‖position‖ := by
  have zeroRemainder : conjugateInversePowerTaylorRemainder displacement power 0 = 0 := by
    simp [conjugateInversePowerTaylorRemainder]
  simpa only [zeroRemainder, sub_zero] using
    conjugateInversePowerTaylorRemainder_difference_bound displacement power radiusNonnegative positive
      separated positionBound (show ‖(0 : ℂ)‖ ≤ radius by simpa using radiusNonnegative)

theorem conjugateInversePowerTaylorRemainder_receiver_difference_bound
    (anchor first second position : ℂ) (power : ℕ) {radius travel distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (separated : radius + travel + distance ≤ ‖anchor‖) (positionBound : ‖position‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖conjugateInversePowerTaylorRemainder first power position -
      conjugateInversePowerTaylorRemainder second power position‖ ≤
      ((power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius *
        ‖position‖) * ‖first - second‖ := by
  let derivative := fun current : ℂ =>
    ((-(power + 1 : ℂ) * conjugateInversePowerTaylorRemainder current (power + 1) position) •
      (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  have displacementSeparated (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      radius + distance ≤ ‖current‖ := by
    have within := mem_closedBall.mp inside
    rw [dist_eq_norm] at within
    have triangle := norm_add_le (anchor - current) current
    rw [sub_add_cancel, norm_sub_rev anchor current] at triangle
    linarith
  have actual (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      HasFDerivAt (fun displacement => conjugateInversePowerTaylorRemainder displacement power position)
        (derivative current) current := by
    have lower := displacementSeparated current inside
    have triangle := norm_add_le (current - position) position
    rw [sub_add_cancel] at triangle
    have sourceGap : distance ≤ ‖current - position‖ := by linarith
    exact conjugateInversePowerTaylorRemainder_receiver_hasFDerivAt current position power
      (norm_pos_iff.mp (by linarith : 0 < ‖current‖)) (norm_pos_iff.mp (positive.trans_le sourceGap))
  have bounded (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      ‖derivative current‖ ≤
        (power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius * ‖position‖ := by
    have remainder := conjugateInversePowerTaylorRemainder_norm_le current position (power + 1)
      radiusNonnegative positive (displacementSeparated current inside) positionBound
    have degreeNorm : ‖(-(power + 1 : ℂ))‖ = (power + 1 : ℝ) := by
      simpa only [norm_neg, Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (power + 1)
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    change ‖(-(power + 1 : ℂ) * conjugateInversePowerTaylorRemainder current (power + 1) position) *
      star direction‖ ≤ _
    rw [norm_mul, norm_mul, degreeNorm, norm_star]
    have scaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left remainder (by positivity : 0 ≤ (power + 1 : ℝ))) (norm_nonneg direction)
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at scaled
    convert scaled using 1 <;> ring
  have estimate := (convex_closedBall anchor travel).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun current inside => (actual current inside).hasFDerivWithinAt) bounded
    (mem_closedBall.mpr (by simpa only [dist_eq_norm] using firstBound))
    (mem_closedBall.mpr (by simpa only [dist_eq_norm] using secondBound))
  simpa only [norm_sub_rev] using estimate

end EulerNonuniqueness.Section6
