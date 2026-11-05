import EulerNonuniqueness.Section6.ExteriorInversePowerBound
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

def exteriorVorticityCoefficient (vorticity : Vorticity) (center : ℂ) (radius : ℝ) (power : ℕ) : ℂ :=
  ((-1 : ℂ) ^ (power + 1) * Complex.I * (radius : ℂ) ^ power / ((2 * Real.pi : ℝ) : ℂ)) *
    ∫ position : ℂ, vorticity position • (star (center - position))⁻¹ ^ (power + 2)

theorem norm_exteriorVorticityCoefficient_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (power : ℕ) :
    ‖exteriorVorticityCoefficient vorticity center radius power‖ ≤
      (radius / distance) ^ power *
        ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi)) := by
  unfold exteriorVorticityCoefficient
  simp only [norm_mul, norm_div, norm_pow, norm_neg, norm_one, one_pow, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg radiusNonnegative,
    abs_of_pos (by positivity : 0 < 2 * Real.pi), one_mul]
  have estimate := norm_integral_exterior_inverse_power integrable center positive separated power
  have scaled := mul_le_mul_of_nonneg_left estimate (by positivity : 0 ≤ radius ^ power / (2 * Real.pi))
  convert scaled using 1 <;> simp only [div_pow, inv_pow, abs_mul, abs_of_pos Real.pi_pos] <;> norm_num <;> ring

theorem summable_weighted_exteriorVorticityCoefficient {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * radius / distance < 1) :
    Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) := by
  have geometric := (summable_geometric_of_lt_one (by positivity : 0 ≤ 2 * radius / distance) small).mul_right
    (2 * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi)))
  apply Summable.of_nonneg_of_le (fun power => by positivity) (fun power => ?_) geometric
  have estimate := mul_le_mul_of_nonneg_left
    (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative positive separated power)
    (by positivity : 0 ≤ (2 : ℝ) ^ (power + 1))
  convert estimate using 1
  rw [show 2 * radius / distance = 2 * (radius / distance) by ring, mul_pow, pow_succ]
  ring

theorem tsum_weighted_exteriorVorticityCoefficient_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * radius / distance < 1) :
    (∑' power : ℕ, (2 : ℝ) ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) ≤
      (1 - 2 * radius / distance)⁻¹ *
        (2 * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi))) := by
  have nonnegative : 0 ≤ 2 * radius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one nonnegative small).mul_right
    (2 * ((∫ position, inverseSquareVorticityWeight vorticity center position) / (2 * Real.pi)))
  have estimate := tsum_le_tsum (fun power => ?_)
    (summable_weighted_exteriorVorticityCoefficient integrable center radiusNonnegative positive separated small) geometric
  · simpa only [tsum_mul_right, tsum_geometric_of_lt_one nonnegative small] using estimate
  · have scaled := mul_le_mul_of_nonneg_left
      (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative positive separated power)
      (by positivity : 0 ≤ (2 : ℝ) ^ (power + 1))
    convert scaled using 1
    rw [show 2 * radius / distance = 2 * (radius / distance) by ring, mul_pow, pow_succ]
    ring

end EulerNonuniqueness.Section6
