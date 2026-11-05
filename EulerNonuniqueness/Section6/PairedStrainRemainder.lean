import EulerNonuniqueness.Section6.QuadrupoleFarField

noncomputable section

namespace EulerNonuniqueness.Section6

def cauchyStrainTaylorRemainder (position : ℂ) : ℂ :=
  1 / (1 - position) ^ 2 - 1 - 2 * position - 3 * position ^ 2

def cauchyStrainTaylorRemainderDerivative (position : ℂ) : ℂ :=
  position ^ 2 * (12 - 16 * position + 6 * position ^ 2) / (1 - position) ^ 3

theorem cauchyStrainTaylorRemainder_hasDerivAt {position : ℂ} (nonzero : 1 - position ≠ 0) :
    HasDerivAt cauchyStrainTaylorRemainder (cauchyStrainTaylorRemainderDerivative position) position := by
  have denominator := ((hasDerivAt_const position (1 : ℂ)).sub (hasDerivAt_id position)).pow 2
  have inverse := denominator.inv (pow_ne_zero 2 nonzero)
  have derivative := ((inverse.sub_const 1).sub ((hasDerivAt_id position).const_mul 2)).sub
    (((hasDerivAt_id position).pow 2).const_mul 3)
  convert derivative using 1
  · funext current
    simp only [cauchyStrainTaylorRemainder, one_div, id_eq]
  · dsimp [cauchyStrainTaylorRemainderDerivative]
    field_simp [nonzero]
    ring

theorem cauchyStrainTaylorRemainderDerivative_bound {position : ℂ} (small : ‖position‖ ≤ 1 / 2) :
    ‖cauchyStrainTaylorRemainderDerivative position‖ ≤ 176 * ‖position‖ ^ 2 := by
  have inverse := norm_inv_one_sub_le_two small
  have numerator : ‖12 - 16 * position + 6 * position ^ 2‖ ≤ 22 := by
    have triangle := (norm_add_le (12 - 16 * position) (6 * position ^ 2)).trans
      (add_le_add_right (norm_sub_le (12 : ℂ) (16 * position)) _)
    norm_num only [norm_mul, norm_pow, Complex.norm_ofNat] at triangle
    nlinarith [norm_nonneg position]
  have inverseCube : ‖((1 - position)⁻¹) ^ 3‖ ≤ 8 := by
    rw [norm_pow]
    nlinarith [pow_le_pow_left₀ (norm_nonneg ((1 - position)⁻¹)) inverse 3]
  unfold cauchyStrainTaylorRemainderDerivative
  rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (‖position‖ ^ 2 * 22) * 8 :=
      mul_le_mul (mul_le_mul_of_nonneg_left numerator (sq_nonneg _)) inverseCube (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem cauchyStrainTaylorRemainder_pair_bound {first second : ℂ} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ 1 / 2)
    (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖cauchyStrainTaylorRemainder first - cauchyStrainTaylorRemainder second‖ ≤
      176 * radius ^ 2 * ‖first - second‖ := by
  have derivative (position : ℂ) (member : position ∈ Metric.closedBall (0 : ℂ) radius) :
      HasDerivWithinAt cauchyStrainTaylorRemainder (cauchyStrainTaylorRemainderDerivative position)
        (Metric.closedBall (0 : ℂ) radius) position := by
    have small : ‖position‖ ≤ 1 / 2 := by
      have : ‖position‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
      exact this.trans radiusSmall
    have nonzero : 1 - position ≠ 0 := by
      intro zero
      have equality : position = 1 := (sub_eq_zero.mp zero).symm
      rw [equality, norm_one] at small
      norm_num at small
    exact (cauchyStrainTaylorRemainder_hasDerivAt nonzero).hasDerivWithinAt
  have bound (position : ℂ) (member : position ∈ Metric.closedBall (0 : ℂ) radius) :
      ‖cauchyStrainTaylorRemainderDerivative position‖ ≤ 176 * radius ^ 2 := by
    have normBound : ‖position‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
    exact (cauchyStrainTaylorRemainderDerivative_bound (normBound.trans radiusSmall)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) normBound 2) (by norm_num))
  exact (convex_closedBall (0 : ℂ) radius).norm_image_sub_le_of_norm_hasDerivWithin_le derivative bound
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using secondBound)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using firstBound)

end EulerNonuniqueness.Section6
