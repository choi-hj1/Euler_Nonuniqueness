import EulerNonuniqueness.Section3.ExteriorCoefficientWeightedSum
import EulerNonuniqueness.Section6.MovingExteriorCoefficientBound

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem tsum_exteriorVorticityCoefficient_half_weight_le {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {radius distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (small : weight * radius / distance ≤ 1 / 2) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖exteriorVorticityCoefficient vorticity center radius power‖) ≤
      weight / Real.pi * (∫ position, inverseSquareVorticityWeight vorticity center position) := by
  let mass := ∫ position, inverseSquareVorticityWeight vorticity center position
  have massNonnegative : 0 ≤ mass := integral_nonneg fun position => by
    unfold inverseSquareVorticityWeight
    positivity
  have ratioNonnegative : 0 ≤ weight * radius / distance := by positivity
  have ratioSmall : weight * radius / distance < 1 := small.trans_lt (by norm_num)
  apply (tsum_exteriorVorticityCoefficient_weight_le integrable center radiusNonnegative
    positive weightNonnegative separated ratioSmall).trans
  have inverseBound := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
    (show 1 / 2 ≤ 1 - weight * radius / distance by linarith)
  norm_num only [one_div, inv_inv] at inverseBound
  have multiplied := mul_le_mul_of_nonneg_right inverseBound
    (show 0 ≤ weight * (mass / (2 * Real.pi)) by positivity)
  convert multiplied using 1 <;> ring

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

theorem tsum_exteriorTaylorCoefficient_weight_le {count : ℕ}
    (family : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (center : ℝ → ℂ) (radius time : ℝ) {distance weight : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : ∀ source ∈ selected, ∀ position ∈ (family.patch source).domain time,
      distance ≤ ‖center time - position‖) (small : weight * radius / distance ≤ 1 / 2) :
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖family.exteriorTaylorCoefficient selected center radius (power + 1) time‖) ≤
      weight / Real.pi * (∫ position, Section6.inverseSquareVorticityWeight
        (family.subfamilyVorticity selected time) (center time) position) := by
  simp_rw [family.exteriorTaylorCoefficient_eq_vorticityCoefficient selected center radius time _ positive separated]
  exact Section6.tsum_exteriorVorticityCoefficient_half_weight_le
    (family.subfamilyVorticity_integrable selected time) (center time) radiusNonnegative positive weightNonnegative
    (family.subfamily_support_separated selected (center time) time distance separated) small

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
