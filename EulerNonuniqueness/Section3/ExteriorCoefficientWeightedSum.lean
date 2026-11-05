import EulerNonuniqueness.Section3.ExteriorCoefficientWeights

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem tsum_exteriorVorticityCoefficient_weight_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : weight * radius / distance < 1) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) ≤
      (1 - weight * radius / distance)⁻¹ *
        (weight * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi))) := by
  have nonnegative : 0 ≤ weight * radius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one nonnegative small).mul_right
    (weight * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi)))
  have estimate := tsum_le_tsum (fun power => ?_)
    (summable_exteriorVorticityCoefficient_weight integrable center radiusNonnegative positive
      weightNonnegative separated small) geometric
  · simpa only [tsum_mul_right, tsum_geometric_of_lt_one nonnegative small] using estimate
  · have scaled := mul_le_mul_of_nonneg_left
      (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative positive separated power)
      (pow_nonneg weightNonnegative (power + 1))
    convert scaled using 1
    rw [show weight * radius / distance = weight * (radius / distance) by ring, mul_pow, pow_succ]
    ring

end EulerNonuniqueness.Section6
