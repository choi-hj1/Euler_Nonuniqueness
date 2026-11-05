import EulerNonuniqueness.Section6.ExteriorCoefficientCenterDifference

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem exteriorCoefficientCenter_weighted_term_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (first second : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (firstSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖second - position‖)
    (power : ℕ) :
    weight ^ (power + 1) * ‖exteriorVorticityCoefficient vorticity first radius power -
      exteriorVorticityCoefficient vorticity second radius power‖ ≤
      (4 * weight * ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi))) *
        (2 * weight * radius / distance) ^ power := by
  have degreeBound : (power + 2 : ℝ) ≤ (2 : ℝ) ^ (power + 2) := by
    exact_mod_cast (Nat.lt_two_pow_self (n := power + 2)).le
  have degreeBound' : (power + 2 : ℝ) ≤ 4 * (2 : ℝ) ^ power := by
    simpa only [pow_add, show (2 : ℝ) ^ 2 = 4 by norm_num, mul_comm] using degreeBound
  have massNonnegative : 0 ≤ ∫ position, |vorticity position| := integral_nonneg fun _ => abs_nonneg _
  have actual := mul_le_mul_of_nonneg_left
    (exteriorVorticityCoefficient_center_difference_norm_le integrable first second radiusNonnegative positive
      firstSeparated secondSeparated power) (pow_nonneg weightNonnegative (power + 1))
  apply actual.trans
  calc
    _ ≤ weight ^ (power + 1) * ((4 * (2 : ℝ) ^ power) * (radius / distance) ^ power *
        ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi))) := by
      gcongr
    _ = _ := by rw [pow_succ]; simp only [div_pow, mul_pow]; ring

theorem summable_weighted_exteriorCoefficientCenter_difference {vorticity : Vorticity}
    (integrable : Integrable vorticity) (first second : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (firstSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖second - position‖)
    (small : 2 * weight * radius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity first radius power -
        exteriorVorticityCoefficient vorticity second radius power‖) := by
  have geometric := (summable_geometric_of_lt_one
    (by positivity : 0 ≤ 2 * weight * radius / distance) small).mul_left
      (4 * weight * ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi)))
  exact Summable.of_nonneg_of_le (fun power => by positivity)
    (fun power => exteriorCoefficientCenter_weighted_term_le integrable first second radiusNonnegative positive
      weightNonnegative firstSeparated secondSeparated power) geometric

theorem tsum_weighted_exteriorCoefficientCenter_difference_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (first second : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (firstSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖first - position‖)
    (secondSeparated : ∀ position ∈ Function.support vorticity, distance ≤ ‖second - position‖)
    (small : 2 * weight * radius / distance < 1) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity first radius power -
        exteriorVorticityCoefficient vorticity second radius power‖) ≤
      (4 * weight * ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi))) *
        (1 - 2 * weight * radius / distance)⁻¹ := by
  have geometric := (summable_geometric_of_lt_one
    (by positivity : 0 ≤ 2 * weight * radius / distance) small).mul_left
      (4 * weight * ((distance⁻¹ ^ 3 * ‖first - second‖ * ∫ position, |vorticity position|) / (2 * Real.pi)))
  have actual := tsum_le_tsum
    (fun power => exteriorCoefficientCenter_weighted_term_le integrable first second radiusNonnegative positive
      weightNonnegative firstSeparated secondSeparated power)
    (summable_weighted_exteriorCoefficientCenter_difference integrable first second radiusNonnegative positive
      weightNonnegative firstSeparated secondSeparated small) geometric
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one
    (by positivity : 0 ≤ 2 * weight * radius / distance) small] using actual

end EulerNonuniqueness.Section6
