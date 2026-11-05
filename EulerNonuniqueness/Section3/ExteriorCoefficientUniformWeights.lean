import EulerNonuniqueness.Section3.ExteriorCoefficientWeightedSum

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem tsum_exteriorVorticityCoefficient_weight_le_uniform {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight bound : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (boundNonnegative : 0 ≤ bound)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * weight * radius ≤ distance)
    (weightBound : (∫ position, inverseSquareVorticityWeight vorticity center position) ≤ bound) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) ≤ weight * bound / Real.pi := by
  have ratioBound : weight * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  have ratioSmall : weight * radius / distance < 1 := by linarith
  have inverseBound : (1 - weight * radius / distance)⁻¹ ≤ 2 := by
    rw [← one_div]
    apply (one_div_le (by linarith : 0 < 1 - weight * radius / distance) (by norm_num : (0 : ℝ) < 2)).mpr
    linarith
  have integralNonnegative : 0 ≤ ∫ position, inverseSquareVorticityWeight vorticity center position := by
    apply integral_nonneg
    intro position
    unfold inverseSquareVorticityWeight
    positivity
  refine (tsum_exteriorVorticityCoefficient_weight_le integrable center radiusNonnegative positive
    weightNonnegative separated ratioSmall).trans ?_
  calc
    _ ≤ 2 * (weight * (bound / (2 * Real.pi))) :=
      mul_le_mul inverseBound
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right weightBound (by positivity)) weightNonnegative)
        (by positivity) (by norm_num)
    _ = _ := by ring

def exteriorHigherVorticityCoefficient (vorticity : Vorticity) (center : ℂ) (radius : ℝ) (power : ℕ) : ℂ :=
  if power = 0 then 0 else exteriorVorticityCoefficient vorticity center radius power

theorem exteriorHigherVorticityCoefficient_weight_bound {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight bound : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (boundNonnegative : 0 ≤ bound)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * weight * radius ≤ distance)
    (weightBound : (∫ position, inverseSquareVorticityWeight vorticity center position) ≤ bound)
    (power : ℕ) :
    weight ^ (power + 1) * ‖exteriorHigherVorticityCoefficient vorticity center radius power‖ ≤
      (weight ^ 2 * radius * bound / (Real.pi * distance)) * (1 / 2 : ℝ) ^ power := by
  have ratioNonnegative : 0 ≤ weight * radius / distance := by positivity
  have ratioBound : weight * radius / distance ≤ 1 / 2 := (div_le_iff₀ positive).mpr (by linarith)
  cases power with
  | zero =>
      simp only [exteriorHigherVorticityCoefficient, ite_true, norm_zero, mul_zero, pow_zero, mul_one]
      positivity
  | succ power =>
      simp only [exteriorHigherVorticityCoefficient, Nat.succ_ne_zero, if_false]
      have estimate := (norm_exteriorVorticityCoefficient_le integrable center radiusNonnegative positive separated (power + 1)).trans
        (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right weightBound (by positivity)) (by positivity))
      have geometric := pow_le_pow_left₀ ratioNonnegative ratioBound power
      calc
        _ ≤ weight ^ (power + 1 + 1) * ((radius / distance) ^ (power + 1) * (bound / (2 * Real.pi))) :=
          mul_le_mul_of_nonneg_left estimate (by positivity)
        _ = (weight * (weight * radius / distance) * (bound / (2 * Real.pi))) *
            (weight * radius / distance) ^ power := by
          rw [show weight * radius / distance = weight * (radius / distance) by ring, mul_pow,
            pow_succ, pow_succ]
          ring
        _ ≤ (weight * (weight * radius / distance) * (bound / (2 * Real.pi))) * (1 / 2 : ℝ) ^ power :=
          mul_le_mul_of_nonneg_left geometric (by positivity)
        _ = _ := by rw [pow_succ]; ring

theorem tsum_exteriorHigherVorticityCoefficient_weight_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight bound : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (boundNonnegative : 0 ≤ bound)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : 2 * weight * radius ≤ distance)
    (weightBound : (∫ position, inverseSquareVorticityWeight vorticity center position) ≤ bound) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖exteriorHigherVorticityCoefficient vorticity center radius power‖) ≤
      2 * weight ^ 2 * radius * bound / (Real.pi * distance) := by
  have geometric := (hasSum_geometric_of_norm_lt_one (ξ := (1 / 2 : ℝ)) (by norm_num)).mul_left
    (weight ^ 2 * radius * bound / (Real.pi * distance))
  have pointwise := exteriorHigherVorticityCoefficient_weight_bound integrable center radiusNonnegative positive
    weightNonnegative boundNonnegative separated small weightBound
  have summable := Summable.of_nonneg_of_le (fun power => by positivity) pointwise geometric.summable
  have estimate := Summable.tsum_le_tsum pointwise summable geometric.summable
  rw [geometric.tsum_eq] at estimate
  convert estimate using 1 <;> norm_num <;> ring

end EulerNonuniqueness.Section6
