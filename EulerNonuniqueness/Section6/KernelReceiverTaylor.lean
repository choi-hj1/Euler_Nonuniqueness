import EulerNonuniqueness.Section6.PatchKernelTaylor

noncomputable section

namespace EulerNonuniqueness.Section6

theorem biotSavart_receiver_taylor_bound {position center source : ℂ} {distance : ℝ}
    (positive : 0 < distance) (separated : distance ≤ ‖center - source‖)
    (near : 2 * ‖position - center‖ ≤ distance) :
    ‖biotSavartKernel (position - source) - biotSavartKernel (center - source) +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((position - center) / (center - source) ^ 2)‖ ≤
      ‖position - center‖ ^ 2 / (Real.pi * distance ^ 3) := by
  have flip (first second : ℂ) : biotSavartKernel (first - second) = -biotSavartKernel (second - first) := by
    rw [← biotSavartKernel_neg]
    congr 1
    abel
  have denominator : (source - center) ^ 2 = (center - source) ^ 2 := by ring
  have identity :
      biotSavartKernel (position - source) - biotSavartKernel (center - source) +
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((position - center) / (center - source) ^ 2) =
      -(biotSavartKernel (source - position) - biotSavartKernel (source - center) -
        (Complex.I / ((2 * Real.pi : ℝ) : ℂ)) *
          starRingEnd ℂ ((position - center) / (source - center) ^ 2)) := by
    rw [flip position source, flip center source, denominator]
    ring
  rw [identity, norm_neg]
  have estimate := biotSavart_source_taylor_bound (position := source) (source := position) (center := center)
    (radius := ‖position - center‖) (by simpa only [norm_sub_rev] using positive.trans_le separated)
    le_rfl (by simpa only [norm_sub_rev] using near.trans separated)
  apply estimate.trans
  rw [norm_sub_rev source center]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ positive.le separated 3) Real.pi_pos.le)

end EulerNonuniqueness.Section6
