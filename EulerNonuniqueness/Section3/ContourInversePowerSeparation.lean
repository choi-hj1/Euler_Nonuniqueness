import EulerNonuniqueness.Section3.ContourAntiholomorphicFunctional

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem nearCircle_value_norm_lt_two (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) (label : ℝ) : ‖data.val.1 label‖ < 2 := by
  have difference := PeriodicC1HolderHalf.value_bound (data - standardCircleBanach) label
  change ‖data.val.1 label - standardCircle label‖ ≤ ‖data - standardCircleBanach‖ at difference
  have estimate := norm_sub_norm_le (data.val.1 label) (standardCircle label)
  rw [standardCircle_norm] at estimate
  linarith

theorem norm_displacement_sub_mul_lower {displacement scale position : ℂ} {distance : ℝ}
    (positionBound : ‖position‖ ≤ 2) (separated : 2 * ‖scale‖ + distance ≤ ‖displacement‖) :
    distance ≤ ‖displacement - scale * position‖ := by
  have estimate := norm_sub_norm_le displacement (scale * position)
  rw [norm_mul] at estimate
  nlinarith [norm_nonneg scale]

theorem integral_nearCircleInterior_conjugate_inverse_power_eq_functional_of_gap
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (separated : 2 * ‖scale‖ + distance ≤ ‖displacement‖) :
    (∫ position in nearCircleInterior data small,
      (star (displacement - scale * position))⁻¹ ^ (power + 1)) =
      contourAntiholomorphicFunctional
        (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1)) data := by
  apply integral_nearCircleInterior_conjugate_inverse_power_eq_functional data small displacement scale positive power
  · intro position member
    have estimate := nearCircleInterior_subset_ball data small member
    rw [Metric.mem_ball, dist_zero_right] at estimate
    exact norm_displacement_sub_mul_lower (by linarith) separated
  · intro label
    exact norm_displacement_sub_mul_lower (nearCircle_value_norm_lt_two data small label).le separated

theorem contourAntiholomorphicFunctional_inverse_power_fixedRelabel
    (angular : PeriodicC1HolderHalf) (angularSmall : ‖angular‖ < 1 / 2)
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (displacement scale : ℂ) {distance : ℝ} (positive : 0 < distance) (power : ℕ)
    (separated : 2 * ‖scale‖ + distance ≤ ‖displacement‖) :
    contourAntiholomorphicFunctional
        (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1))
        (fixedRelabelEquivalence angular angularSmall data) =
      contourAntiholomorphicFunctional
        (fun position => (star (displacement - scale * position))⁻¹ ^ (power + 1)) data := by
  apply contourAntiholomorphicFunctional_fixedRelabel_of_continuous_comp
  apply Continuous.pow
  apply Continuous.inv₀
  · exact (continuous_const.sub (continuous_const.mul data.val.1.continuous)).star
  · intro label
    apply star_ne_zero.mpr
    exact norm_pos_iff.mp (positive.trans_le (norm_displacement_sub_mul_lower
      (nearCircle_value_norm_lt_two data small label).le separated))

end EulerNonuniqueness.Paper
