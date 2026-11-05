import EulerNonuniqueness.Section6.InversePowerTaylorRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem signed_inverse_power_relative_identity {Index : Type*}
    (selected : Finset Index) (weights : Index → ℝ) (first second : Index → ℂ)
    (displacement : ℂ) (power : ℕ) :
    (∑ index ∈ selected, weights index • (star (displacement - first index))⁻¹ ^ (power + 1)) -
        (∑ index ∈ selected, weights index • (star (displacement - second index))⁻¹ ^ (power + 1)) =
      ((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2)) *
        star (∑ index ∈ selected, weights index • (first index - second index)) +
      ∑ index ∈ selected, weights index •
        (conjugateInversePowerTaylorRemainder displacement power (first index) -
          conjugateInversePowerTaylorRemainder displacement power (second index)) := by
  have momentIdentity :
      ((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2)) *
        star (∑ index ∈ selected, weights index • (first index - second index)) =
      ∑ index ∈ selected, weights index •
        (((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2)) * star (first index - second index)) := by
    have conjugateSmul (coefficient : ℝ) (point : ℂ) :
        star (coefficient • point) = coefficient • star point := by
      change Complex.conjCLE (coefficient • point) = coefficient • Complex.conjCLE point
      exact map_smul Complex.conjCLE coefficient point
    rw [star_sum]
    simp_rw [conjugateSmul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    simp only [Complex.real_smul]
    ring
  rw [momentIdentity, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  simp only [conjugateInversePowerTaylorRemainder, Complex.real_smul, star_sub]
  ring

theorem signed_inverse_power_relative_bound {Index : Type*}
    (selected : Finset Index) (weights : Index → ℝ) (first second : Index → ℂ)
    (displacement : ℂ) (power : ℕ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ index ∈ selected, ‖first index‖ ≤ radius)
    (secondBound : ∀ index ∈ selected, ‖second index‖ ≤ radius) :
    ‖(∑ index ∈ selected, weights index • (star (displacement - first index))⁻¹ ^ (power + 1)) -
      (∑ index ∈ selected, weights index • (star (displacement - second index))⁻¹ ^ (power + 1))‖ ≤
      ((power + 1 : ℝ) * distance⁻¹ ^ (power + 2)) *
        ‖∑ index ∈ selected, weights index • (first index - second index)‖ +
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) *
        ∑ index ∈ selected, |weights index| * ‖first index - second index‖ := by
  have displacementSeparated : distance ≤ ‖displacement‖ := by linarith
  have coefficientBound : ‖((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2))‖ ≤
      (power + 1 : ℝ) * distance⁻¹ ^ (power + 2) := by
    have degreeNorm : ‖(power + 1 : ℂ)‖ = (power + 1 : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (power + 1)
    rw [norm_mul, degreeNorm, norm_pow, norm_inv, norm_star]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg displacement))
        (inv_anti₀ positive displacementSeparated) (power + 2)) (by positivity)
  have firstTerm : ‖((power + 1 : ℂ) * (star displacement)⁻¹ ^ (power + 2)) *
      star (∑ index ∈ selected, weights index • (first index - second index))‖ ≤
      ((power + 1 : ℝ) * distance⁻¹ ^ (power + 2)) *
        ‖∑ index ∈ selected, weights index • (first index - second index)‖ := by
    rw [norm_mul, norm_star]
    exact mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg _)
  have secondTerm : ‖∑ index ∈ selected, weights index •
      (conjugateInversePowerTaylorRemainder displacement power (first index) -
        conjugateInversePowerTaylorRemainder displacement power (second index))‖ ≤
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) *
        ∑ index ∈ selected, |weights index| * ‖first index - second index‖ := by
    apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index member
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left
      (conjugateInversePowerTaylorRemainder_difference_bound displacement power radiusNonnegative positive separated
        (firstBound index member) (secondBound index member)) (abs_nonneg _)).trans_eq (by ring)
  rw [signed_inverse_power_relative_identity selected weights first second displacement power]
  exact (norm_add_le _ _).trans (add_le_add firstTerm secondTerm)

end EulerNonuniqueness.Section6
