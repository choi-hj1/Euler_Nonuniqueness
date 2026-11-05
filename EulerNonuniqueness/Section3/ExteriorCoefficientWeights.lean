import EulerNonuniqueness.Section6.ExteriorCoefficientBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem summable_exteriorVorticityCoefficient_weight {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : weight * radius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) := by
  have geometric := (summable_geometric_of_lt_one
    (by positivity : 0 ≤ weight * radius / distance) small).mul_right
    (weight * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi)))
  apply Summable.of_nonneg_of_le (fun power => by positivity) (fun power => ?_) geometric
  have estimate := mul_le_mul_of_nonneg_left
    (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative positive separated power)
    (pow_nonneg weightNonnegative (power + 1))
  convert estimate using 1
  rw [show weight * radius / distance = weight * (radius / distance) by ring, mul_pow, pow_succ]
  ring

end EulerNonuniqueness.Section6
