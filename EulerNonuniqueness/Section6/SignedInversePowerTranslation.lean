import EulerNonuniqueness.Section6.SignedInversePowerBound

noncomputable section

open Metric

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

theorem signed_inverse_power_hasFDerivAt {Index : Type*}
    (selected : Finset Index) (weights : Index → ℝ) (positions : Index → ℂ)
    (displacement : ℂ) (power : ℕ)
    (noncollision : ∀ index ∈ selected, displacement - positions index ≠ 0) :
    HasFDerivAt (fun current : ℂ =>
        ∑ index ∈ selected, weights index • (star (current - positions index))⁻¹ ^ (power + 1))
      ((-(power + 1 : ℂ) *
        (∑ index ∈ selected, weights index • (star (displacement - positions index))⁻¹ ^ (power + 2))) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) displacement := by
  have derivative := HasFDerivAt.sum (u := selected) (fun index member =>
    ((conjugateInversePower_hasFDerivAt (noncollision index member) power).comp displacement
      ((hasFDerivAt_id (𝕜 := ℝ) displacement).sub_const (positions index))).const_smul (weights index))
  convert derivative using 1
  apply ContinuousLinearMap.ext
  intro direction
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    starRingEnd_apply, Complex.real_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem signed_inverse_power_translation_bound {Index : Type*}
    (selected : Finset Index) (weights : Index → ℝ) (positions : Index → ℂ)
    (zeroMass : ∑ index ∈ selected, weights index = 0)
    (anchor first second : ℂ) (power : ℕ) {radius travel distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (separated : radius + travel + distance ≤ ‖anchor‖)
    (positionBound : ∀ index ∈ selected, ‖positions index‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖(∑ index ∈ selected, weights index • (star (first - positions index))⁻¹ ^ (power + 1)) -
      (∑ index ∈ selected, weights index • (star (second - positions index))⁻¹ ^ (power + 1))‖ ≤
      (((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3)) *
          ‖∑ index ∈ selected, weights index • positions index‖ +
        ((power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius) *
          ∑ index ∈ selected, |weights index| * ‖positions index‖) * ‖first - second‖ := by
  let derivative := fun current : ℂ =>
    ((-(power + 1 : ℂ) *
      (∑ index ∈ selected, weights index • (star (current - positions index))⁻¹ ^ (power + 2))) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  have displacementSeparated (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      radius + distance ≤ ‖current‖ := by
    have within := mem_closedBall.mp inside
    rw [dist_eq_norm] at within
    have triangle := norm_add_le (anchor - current) current
    rw [sub_add_cancel, norm_sub_rev anchor current] at triangle
    linarith
  have actual (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      HasFDerivAt (fun displacement : ℂ =>
        ∑ index ∈ selected, weights index • (star (displacement - positions index))⁻¹ ^ (power + 1))
        (derivative current) current := by
    apply signed_inverse_power_hasFDerivAt
    intro index member
    have triangle := norm_add_le (current - positions index) (positions index)
    rw [sub_add_cancel] at triangle
    have gap : distance ≤ ‖current - positions index‖ := by
      linarith [displacementSeparated current inside, positionBound index member]
    exact norm_pos_iff.mp (positive.trans_le gap)
  have bounded (current : ℂ) (inside : current ∈ closedBall anchor travel) :
      ‖derivative current‖ ≤
        ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3)) *
            ‖∑ index ∈ selected, weights index • positions index‖ +
          ((power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius) *
            ∑ index ∈ selected, |weights index| * ‖positions index‖ := by
    have sourceBound := signed_inverse_power_bound selected weights positions zeroMass current (power + 1)
      radiusNonnegative positive (displacementSeparated current inside) positionBound
    have degreeNorm : ‖(-(power + 1 : ℂ))‖ = (power + 1 : ℝ) := by
      simpa only [norm_neg, Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (power + 1)
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    change ‖(-(power + 1 : ℂ) *
      (∑ index ∈ selected, weights index • (star (current - positions index))⁻¹ ^ (power + 2))) *
        star direction‖ ≤ _
    rw [norm_mul, norm_mul, degreeNorm, norm_star]
    have scaled := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left sourceBound (by positivity : 0 ≤ (power + 1 : ℝ))) (norm_nonneg direction)
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.reduceAdd] at scaled
    convert scaled using 1 <;> ring
  have estimate := (convex_closedBall anchor travel).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun current inside => (actual current inside).hasFDerivWithinAt) bounded
    (mem_closedBall.mpr (by simpa only [dist_eq_norm] using firstBound))
    (mem_closedBall.mpr (by simpa only [dist_eq_norm] using secondBound))
  simpa only [norm_sub_rev] using estimate

end EulerNonuniqueness.Section6
