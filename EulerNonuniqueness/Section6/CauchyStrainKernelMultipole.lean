import EulerNonuniqueness.Section6.PairedDipoleStrain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem cauchyStrainTaylorRemainder_norm_bound {position : ℂ} (small : ‖position‖ ≤ 1 / 2) :
    ‖cauchyStrainTaylorRemainder position‖ ≤ 176 * ‖position‖ ^ 3 := by
  have estimate := cauchyStrainTaylorRemainder_pair_bound (norm_nonneg position) small le_rfl
    (show ‖(0 : ℂ)‖ ≤ ‖position‖ by simpa only [norm_zero] using norm_nonneg position)
  have zero : cauchyStrainTaylorRemainder 0 = 0 := by norm_num [cauchyStrainTaylorRemainder]
  rw [zero, sub_zero, sub_zero] at estimate
  exact estimate.trans_eq (by ring)

theorem cauchyStrain_kernel_multipole_bound {location center source : ℂ} {radius : ℝ}
    (locationPositive : 0 < ‖location - center‖) (sourceBound : ‖source - center‖ ≤ radius)
    (separated : 2 * radius ≤ ‖location - center‖) :
    ‖1 / (location - source) ^ 2 - 1 / (location - center) ^ 2 -
        2 * (source - center) / (location - center) ^ 3 -
        3 * (source - center) ^ 2 / (location - center) ^ 4‖ ≤
      176 * radius ^ 3 / ‖location - center‖ ^ 5 := by
  have radiusNonnegative : 0 ≤ radius := (norm_nonneg _).trans sourceBound
  have differencePositive : 0 < ‖location - source‖ := by
    have triangle := norm_add_le (location - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith
  have difference : (location - center) - (source - center) = location - source := by abel
  have identity := cauchyStrainTaylorRemainder_scaled (norm_pos_iff.mp locationPositive)
    (show (location - center) - (source - center) ≠ 0 by rw [difference]; exact norm_pos_iff.mp differencePositive)
  rw [difference] at identity
  rw [← identity, norm_div, norm_pow]
  have quotientBound : ‖(source - center) / (location - center)‖ ≤ radius / ‖location - center‖ := by
    rw [norm_div]
    exact div_le_div_of_nonneg_right sourceBound locationPositive.le
  have quotientSmall : ‖(source - center) / (location - center)‖ ≤ 1 / 2 :=
    quotientBound.trans ((div_le_iff₀ locationPositive).mpr (by linarith))
  have estimate := (cauchyStrainTaylorRemainder_norm_bound quotientSmall).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) quotientBound 3) (by norm_num))
  exact (div_le_div_of_nonneg_right estimate (sq_nonneg _)).trans_eq (by ring)

end EulerNonuniqueness.Section6
