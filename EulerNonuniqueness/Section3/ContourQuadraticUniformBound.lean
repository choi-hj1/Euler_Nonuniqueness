import EulerNonuniqueness.Section3.ContourQuadraticIntegral
import EulerNonuniqueness.Section3.ComplexContourPerturbation

open Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem contourCauchyKernelQuadratic_uniform_majorized
    (data first second : PeriodicC1HolderHalf) {radius : ℝ}
    (small : radius < 2 / (3 * Real.pi))
    (near : ‖data - standardCircleBanach‖ ≤ radius) (target : ℝ)
    {source : ℝ} (inside : source ∈ Icc (target - Real.pi) (target + Real.pi)) :
    ‖contourCauchyKernelQuadratic data first second target source‖ ≤
      (2 * (radius + ‖standardCircleBanach‖) * ‖first‖ * ‖second‖ /
        (2 / (3 * Real.pi) - radius) ^ 3) * inverseSqrtDistance target source := by
  have chord_positive : 0 < 2 / (3 * Real.pi) - radius := sub_pos.mpr small
  have norm_bound : ‖data‖ ≤ radius + ‖standardCircleBanach‖ := by
    calc
      _ = ‖(data - standardCircleBanach) + standardCircleBanach‖ := by congr 1; abel
      _ ≤ ‖data - standardCircleBanach‖ + ‖standardCircleBanach‖ :=
        norm_add_le (data - standardCircleBanach) standardCircleBanach
      _ ≤ _ := add_le_add_right near _
  by_cases equal : source = target
  · subst source
    simp [contourCauchyKernelQuadratic, inverseSqrtDistance]
  · have nearby : |source - target| ≤ 3 * Real.pi / 2 := by
      rw [abs_le]
      constructor <;> linarith [inside.1, inside.2, Real.pi_pos]
    have chord_bound : (2 / (3 * Real.pi) - radius) * |target - source| ≤
        ‖data.val.1 target - data.val.1 source‖ := by
      apply le_trans _ (PeriodicC1HolderHalf.chord_bound_extended data nearby)
      rw [abs_sub_comm source target]
      exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
    have estimate := contourCauchyKernelQuadratic_weak_bound data first second equal
      chord_positive chord_bound
    calc
      _ ≤ 2 * ‖data‖ * ‖first‖ * ‖second‖ /
          ((2 / (3 * Real.pi) - radius) ^ 3 * Real.sqrt |target - source|) := estimate
      _ ≤ 2 * (radius + ‖standardCircleBanach‖) * ‖first‖ * ‖second‖ /
          ((2 / (3 * Real.pi) - radius) ^ 3 * Real.sqrt |target - source|) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left norm_bound (by norm_num)) (norm_nonneg first))
            (norm_nonneg second)) (by positivity)
      _ = _ := by
        simp only [inverseSqrtDistance, abs_sub_comm target source, div_eq_mul_inv, mul_inv]
        ring

end

end EulerNonuniqueness.Paper
