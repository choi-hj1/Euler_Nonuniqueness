import EulerNonuniqueness.Section6.PatchSelfInteraction

noncomputable section

namespace EulerNonuniqueness.Section6

theorem inverse_source_taylor_identity {position source center : ℂ}
    (centerNonzero : position - center ≠ 0) (sourceNonzero : position - source ≠ 0) :
    (position - source)⁻¹ - (position - center)⁻¹ -
        (source - center) / (position - center) ^ 2 =
      (source - center) ^ 2 / ((position - center) ^ 2 * (position - source)) := by
  field_simp
  <;> ring

theorem inverse_source_taylor_bound {position source center : ℂ} {radius : ℝ}
    (distancePositive : 0 < ‖position - center‖)
    (sourceBound : ‖source - center‖ ≤ radius)
    (separated : 2 * radius ≤ ‖position - center‖) :
    ‖(position - source)⁻¹ - (position - center)⁻¹ -
        (source - center) / (position - center) ^ 2‖ ≤
      2 * radius ^ 2 / ‖position - center‖ ^ 3 := by
  have differenceBound : ‖position - center‖ / 2 ≤ ‖position - source‖ := by
    have triangle : ‖position - center‖ ≤ ‖position - source‖ + ‖source - center‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le (position - source) (source - center)
    linarith
  have sourcePositive : 0 < ‖position - source‖ := by linarith
  rw [inverse_source_taylor_identity (norm_pos_iff.mp distancePositive)
    (norm_pos_iff.mp sourcePositive), norm_div, norm_pow, norm_mul, norm_pow]
  have radiusNonnegative : 0 ≤ radius := le_trans (norm_nonneg _) sourceBound
  have numeratorBound : ‖source - center‖ ^ 2 ≤ radius ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) sourceBound 2
  apply (div_le_div_of_nonneg_right numeratorBound (by positivity)).trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have multiplied := mul_le_mul_of_nonneg_left differenceBound
    (show 0 ≤ 2 * radius ^ 2 * ‖position - center‖ ^ 2 by positivity)
  nlinarith

theorem biotSavart_source_taylor_bound {position source center : ℂ} {radius : ℝ}
    (distancePositive : 0 < ‖position - center‖)
    (sourceBound : ‖source - center‖ ≤ radius)
    (separated : 2 * radius ≤ ‖position - center‖) :
    ‖biotSavartKernel (position - source) - biotSavartKernel (position - center) -
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((source - center) / (position - center) ^ 2)‖ ≤
      radius ^ 2 / (Real.pi * ‖position - center‖ ^ 3) := by
  have identity :
      biotSavartKernel (position - source) - biotSavartKernel (position - center) -
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((source - center) / (position - center) ^ 2) =
      (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * starRingEnd ℂ
        ((position - source)⁻¹ - (position - center)⁻¹ -
          (source - center) / (position - center) ^ 2) := by
    rw [biotSavartKernel_eq_conj_inv, biotSavartKernel_eq_conj_inv]
    simp only [map_sub, map_inv₀]
    ring
  rw [identity, norm_mul, Complex.norm_conj]
  have coefficient : ‖Complex.I / ((2 * Real.pi : ℝ) : ℂ)‖ = 1 / (2 * Real.pi) := by
    simp [norm_div, abs_of_pos Real.pi_pos]
  rw [coefficient]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (2 * radius ^ 2 / ‖position - center‖ ^ 3) :=
      mul_le_mul_of_nonneg_left (inverse_source_taylor_bound distancePositive sourceBound separated)
        (by positivity)
    _ = _ := by field_simp <;> ring

end EulerNonuniqueness.Section6
