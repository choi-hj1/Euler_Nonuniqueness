import EulerNonuniqueness.Section6.MovingExteriorCoefficientDerivative
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace EulerNonuniqueness.Section6

private theorem summable_shifted_linear_geometric {ratio : ℝ} (small : ‖ratio‖ < 1) :
    Summable (fun power : ℕ => (power + 2 : ℝ) * ratio ^ power) := by
  have linear := summable_pow_mul_geometric_of_norm_lt_one 1 small
  have constant := (summable_geometric_of_norm_lt_one small).mul_right 2
  convert linear.add constant using 1
  funext power
  simp only [pow_one]
  ring

private theorem summable_shifted_quadratic_geometric {ratio : ℝ} (small : ‖ratio‖ < 1) :
    Summable (fun power : ℕ => (power + 2 : ℝ) * (power + 3 : ℝ) * ratio ^ power) := by
  have quadratic := summable_pow_mul_geometric_of_norm_lt_one 2 small
  have linear := (summable_pow_mul_geometric_of_norm_lt_one 1 small).mul_right 5
  have constant := (summable_geometric_of_norm_lt_one small).mul_right 6
  convert (quadratic.add linear).add constant using 1
  funext power
  simp only [pow_one]
  ring

theorem summable_temporalCoefficientEnvelope {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (small : 4 * radius / distance < 1) (weight mass : ℝ) :
    Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      (((power + 2 : ℕ) : ℝ) * radius ^ power / (2 * Real.pi) *
        (((2 * radius / Real.pi) * distance⁻¹ ^ (power + 1) +
          (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) / (4 * Real.pi)) * weight ^ 2 +
          (mass / Real.pi * distance⁻¹ ^ (power + 2)) * weight))) := by
  have secondSmall : 2 * radius / distance < 1 := by
    have nonnegative : 0 ≤ radius / distance := div_nonneg radiusNonnegative positive.le
    rw [mul_div_assoc] at small ⊢
    linarith
  have first := (summable_shifted_quadratic_geometric (ratio := 4 * radius / distance)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * radius / distance)] using small)).mul_right
      (weight ^ 2 / Real.pi ^ 2)
  have second := (summable_shifted_linear_geometric (ratio := 2 * radius / distance)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * radius / distance)] using secondSmall)).mul_right
      (2 * radius / distance * weight ^ 2 / Real.pi ^ 2 + 5 * weight ^ 2 / (2 * Real.pi ^ 2) +
        mass * weight / (Real.pi ^ 2 * distance ^ 2))
  convert first.add second using 1
  funext power
  simp only [Nat.cast_add, Nat.cast_ofNat, pow_add, pow_succ, div_pow, mul_pow, inv_pow,
    show (4 : ℝ) = 2 * 2 by norm_num]
  ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

open Set MeasureTheory
open EulerNonuniqueness.Section6

theorem summable_weighted_exteriorMaterialCoefficientDerivative {count : ℕ}
    (family : FiniteMovingPatchFamily count) (index : Fin count) {time distance : ℝ}
    (inside : time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (centered : (family.patch index).center =ᶠ[nhds time] (family.patch index).centroid)
    (positive : 0 < distance) (small : 4 * (family.patch index).radius / distance < 1)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖(family.patch index).center time - position‖) :
    Summable (fun power : ℕ => (2 : ℝ) ^ (power + 1) *
      ‖family.exteriorMaterialCoefficientDerivative index power time‖) := by
  have geometrySmall : 4 * (family.patch index).radius ≤ distance :=
    ((div_lt_one positive).mp small).le
  apply Summable.of_nonneg_of_le (fun power => by positivity) (fun power => ?_)
    (summable_temporalCoefficientEnvelope (family.patch index).radius_positive.le positive small
      (∫ position, inverseSquareVorticityWeight (family.subfamilyVorticity (Finset.univ.erase index) time)
        ((family.patch index).center time) position)
      (∫ position, |family.patchVorticity time index position|))
  exact mul_le_mul_of_nonneg_left
    (family.norm_exteriorMaterialCoefficientDerivative_le index inside material centered positive geometrySmall separated power)
    (by positivity)

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
