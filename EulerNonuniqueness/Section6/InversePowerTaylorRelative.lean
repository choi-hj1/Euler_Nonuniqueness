import EulerNonuniqueness.Section6.SmoothConjugateInversePower
import EulerNonuniqueness.Section6.ExteriorCoefficientCenterDifference

noncomputable section

open Metric

namespace EulerNonuniqueness.Section6

def conjugateInversePowerTaylorRemainder (displacement : ℂ) (power : ℕ) (position : ℂ) : ℂ :=
  (star (displacement - position))⁻¹ ^ (power + 1) - (star displacement)⁻¹ ^ (power + 1) -
    (power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2) * star position

theorem conjugateInversePower_hasFDerivAt {position : ℂ} (nonzero : position ≠ 0) (power : ℕ) :
    HasFDerivAt (fun current : ℂ => (star current)⁻¹ ^ (power + 1))
      ((-(power + 1 : ℂ) * (star position)⁻¹ ^ (power + 2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) position := by
  have positive : 0 < ‖position‖ := norm_pos_iff.mpr nonzero
  simpa only [Nat.cast_add, Nat.cast_one] using
    (smoothConjugateInversePower_hasFDerivAt positive power le_rfl).congr_of_eventuallyEq
      (smoothConjugateInversePower_eventuallyEq positive (power + 1) le_rfl).symm

theorem conjugateInversePowerTaylorRemainder_hasFDerivAt (displacement position : ℂ) (power : ℕ)
    (nonzero : displacement - position ≠ 0) :
    HasFDerivAt (conjugateInversePowerTaylorRemainder displacement power)
      (((power + 1 : ℂ) * ((star (displacement - position))⁻¹ ^ (power + 2) -
        (star displacement)⁻¹ ^ (power + 2))) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) position := by
  have affine := (hasFDerivAt_id (𝕜 := ℝ) position).const_sub displacement
  have actual := ((conjugateInversePower_hasFDerivAt nonzero power).comp position affine).sub_const
    ((star displacement)⁻¹ ^ (power + 1))
  have linear := (((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2)) •
    (Complex.conjCLE : ℂ →L[ℝ] ℂ)).hasFDerivAt (x := position)
  convert actual.sub linear using 1
  apply ContinuousLinearMap.ext
  intro direction
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, starRingEnd_apply, star_neg, smul_eq_mul]
  ring

theorem conjugateInversePowerTaylorRemainder_difference_bound (displacement : ℂ) (power : ℕ)
    {radius distance : ℝ} (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    {first second : ℂ} (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖conjugateInversePowerTaylorRemainder displacement power first -
      conjugateInversePowerTaylorRemainder displacement power second‖ ≤
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) * ‖first - second‖ := by
  have displacementSeparated : distance ≤ ‖displacement‖ := by linarith
  have gap (position : ℂ) (inside : position ∈ closedBall (0 : ℂ) radius) : distance ≤ ‖displacement - position‖ := by
    have positionBound := mem_closedBall_zero_iff.mp inside
    have triangle := norm_add_le (displacement - position) position
    rw [sub_add_cancel] at triangle
    linarith
  let derivative := fun position : ℂ =>
    (((power + 1 : ℂ) * ((star (displacement - position))⁻¹ ^ (power + 2) -
      (star displacement)⁻¹ ^ (power + 2))) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
  have actual (position : ℂ) (inside : position ∈ closedBall (0 : ℂ) radius) :
      HasFDerivAt (conjugateInversePowerTaylorRemainder displacement power) (derivative position) position :=
    conjugateInversePowerTaylorRemainder_hasFDerivAt displacement position power
      (norm_pos_iff.mp (positive.trans_le (gap position inside)))
  have bounded (position : ℂ) (inside : position ∈ closedBall (0 : ℂ) radius) :
      ‖derivative position‖ ≤ (power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius := by
    have kernelBound := conjugate_inverse_power_difference_bound positive (gap position inside) displacementSeparated (power + 1)
    have identity : (displacement - position) - displacement = -position := by abel
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one, identity, norm_neg] at kernelBound
    have normalizedKernelBound :
        ‖(star (displacement - position))⁻¹ ^ (power + 2) - (star displacement)⁻¹ ^ (power + 2)‖ ≤
          (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * ‖position‖ := by
      convert kernelBound using 1 <;> ring
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro direction
    change ‖((power + 1 : ℂ) * ((star (displacement - position))⁻¹ ^ (power + 2) -
      (star displacement)⁻¹ ^ (power + 2))) * star direction‖ ≤ _
    have degreeNorm : ‖(power + 1 : ℂ)‖ = (power + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (power + 1)
    rw [norm_mul, norm_mul, degreeNorm, norm_star]
    apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left normalizedKernelBound (by positivity)) (norm_nonneg direction)).trans
    have positionBound := mem_closedBall_zero_iff.mp inside
    have scalar := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left positionBound
      (show 0 ≤ (power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) by positivity))
      (norm_nonneg direction)
    convert scalar using 1 <;> ring
  have estimate := (convex_closedBall (0 : ℂ) radius).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun position inside => (actual position inside).hasFDerivWithinAt) bounded
    (mem_closedBall_zero_iff.mpr firstBound) (mem_closedBall_zero_iff.mpr secondBound)
  simpa only [norm_sub_rev] using estimate

end EulerNonuniqueness.Section6
