import EulerNonuniqueness.Section6.PairedStrainRemainder

noncomputable section

namespace EulerNonuniqueness.Section6

def cauchyHessianTaylorRemainder (position : ℂ) : ℂ :=
  1 / (1 - position) ^ 3 - 1 - 3 * position - 6 * position ^ 2

def cauchyHessianTaylorRemainderDerivative (position : ℂ) : ℂ :=
  position ^ 2 * (30 - 60 * position + 45 * position ^ 2 - 12 * position ^ 3) / (1 - position) ^ 4

theorem cauchyHessianTaylorRemainder_hasDerivAt {position : ℂ} (nonzero : 1 - position ≠ 0) :
    HasDerivAt cauchyHessianTaylorRemainder (cauchyHessianTaylorRemainderDerivative position) position := by
  have denominator := ((hasDerivAt_const position (1 : ℂ)).sub (hasDerivAt_id position)).pow 3
  have inverse := denominator.inv (pow_ne_zero 3 nonzero)
  have derivative := ((inverse.sub_const 1).sub ((hasDerivAt_id position).const_mul 3)).sub
    (((hasDerivAt_id position).pow 2).const_mul 6)
  convert derivative using 1
  · funext current
    simp only [cauchyHessianTaylorRemainder, one_div, id_eq]
  · dsimp [cauchyHessianTaylorRemainderDerivative]
    field_simp [nonzero]
    ring

theorem cauchyHessianTaylorRemainderDerivative_bound {position : ℂ} (small : ‖position‖ ≤ 1 / 2) :
    ‖cauchyHessianTaylorRemainderDerivative position‖ ≤ 1168 * ‖position‖ ^ 2 := by
  have inverse := norm_inv_one_sub_le_two small
  have squareBound : ‖position‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg position]
  have cubeBound : ‖position‖ ^ 3 ≤ 1 / 8 := by
    have estimate := pow_le_pow_left₀ (norm_nonneg position) small 3
    norm_num at estimate ⊢
    exact estimate
  have numerator : ‖30 - 60 * position + 45 * position ^ 2 - 12 * position ^ 3‖ ≤ 73 := by
    have firstTriangle := norm_sub_le (30 : ℂ) (60 * position)
    have secondTriangle := norm_add_le (30 - 60 * position) (45 * position ^ 2)
    have thirdTriangle := norm_sub_le (30 - 60 * position + 45 * position ^ 2) (12 * position ^ 3)
    norm_num only [norm_mul, norm_pow, Complex.norm_ofNat] at firstTriangle secondTriangle thirdTriangle
    linarith
  have inverseFourth : ‖((1 - position)⁻¹) ^ 4‖ ≤ 16 := by
    rw [norm_pow]
    have estimate := pow_le_pow_left₀ (norm_nonneg ((1 - position)⁻¹)) inverse 4
    norm_num at estimate ⊢
    exact estimate
  unfold cauchyHessianTaylorRemainderDerivative
  rw [div_eq_mul_inv, ← inv_pow, norm_mul, norm_mul, norm_pow]
  calc
    _ ≤ (‖position‖ ^ 2 * 73) * 16 :=
      mul_le_mul (mul_le_mul_of_nonneg_left numerator (sq_nonneg _)) inverseFourth (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem cauchyHessianTaylorRemainder_pair_bound {first second : ℂ} {radius : ℝ}
    (radiusNonnegative : 0 ≤ radius) (radiusSmall : radius ≤ 1 / 2)
    (firstBound : ‖first‖ ≤ radius) (secondBound : ‖second‖ ≤ radius) :
    ‖cauchyHessianTaylorRemainder first - cauchyHessianTaylorRemainder second‖ ≤
      1168 * radius ^ 2 * ‖first - second‖ := by
  have derivative (position : ℂ) (member : position ∈ Metric.closedBall (0 : ℂ) radius) :
      HasDerivWithinAt cauchyHessianTaylorRemainder (cauchyHessianTaylorRemainderDerivative position)
        (Metric.closedBall (0 : ℂ) radius) position := by
    have small : ‖position‖ ≤ 1 / 2 := by
      have : ‖position‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
      exact this.trans radiusSmall
    have nonzero : 1 - position ≠ 0 := by
      intro zero
      have equality : position = 1 := (sub_eq_zero.mp zero).symm
      rw [equality, norm_one] at small
      norm_num at small
    exact (cauchyHessianTaylorRemainder_hasDerivAt nonzero).hasDerivWithinAt
  have bound (position : ℂ) (member : position ∈ Metric.closedBall (0 : ℂ) radius) :
      ‖cauchyHessianTaylorRemainderDerivative position‖ ≤ 1168 * radius ^ 2 := by
    have normBound : ‖position‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using member
    exact (cauchyHessianTaylorRemainderDerivative_bound (normBound.trans radiusSmall)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) normBound 2) (by norm_num))
  exact (convex_closedBall (0 : ℂ) radius).norm_image_sub_le_of_norm_hasDerivWithin_le derivative bound
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using secondBound)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using firstBound)

end EulerNonuniqueness.Section6
