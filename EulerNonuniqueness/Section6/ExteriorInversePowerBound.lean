import EulerNonuniqueness.Section6.WeightedCoMovingKernel

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Section6

theorem exterior_inverse_power_weight_bound {vorticity : Vorticity} (center : ℂ)
    {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (power : ℕ) (position : ℂ) :
    ‖vorticity position • (star (center - position))⁻¹ ^ (power + 2)‖ ≤
      distance⁻¹ ^ power * inverseSquareVorticityWeight vorticity center position := by
  by_cases zero : vorticity position = 0
  · simp [zero, inverseSquareVorticityWeight]
  have lower := separated position (Function.mem_support.mpr zero)
  have inverseBound := inv_anti₀ positive lower
  rw [norm_smul, Real.norm_eq_abs, norm_pow, norm_inv, norm_star, pow_add]
  have estimate := pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) inverseBound power
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right estimate (sq_nonneg _))
    (abs_nonneg _)).trans_eq (by unfold inverseSquareVorticityWeight; ring)

theorem integrable_exterior_inverse_power {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (power : ℕ) :
    Integrable (fun position : ℂ => vorticity position • (star (center - position))⁻¹ ^ (power + 2)) := by
  have weight := integrable_inverseSquareVorticityWeight integrable center positive separated
  have kernelMeasurable : Measurable (fun position : ℂ => (star (center - position))⁻¹ ^ (power + 2)) := by
    fun_prop
  exact (weight.const_mul (distance⁻¹ ^ power)).mono'
    (integrable.aestronglyMeasurable.smul kernelMeasurable.aestronglyMeasurable)
    (Filter.Eventually.of_forall (exterior_inverse_power_weight_bound center positive separated power))

theorem norm_integral_exterior_inverse_power {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (power : ℕ) :
    ‖∫ position : ℂ, vorticity position • (star (center - position))⁻¹ ^ (power + 2)‖ ≤
      distance⁻¹ ^ power * ∫ position, inverseSquareVorticityWeight vorticity center position := by
  have estimate := norm_integral_le_of_norm_le
    ((integrable_inverseSquareVorticityWeight integrable center positive separated).const_mul (distance⁻¹ ^ power))
    (Filter.Eventually.of_forall (exterior_inverse_power_weight_bound center positive separated power))
  simpa only [integral_const_mul] using estimate

end EulerNonuniqueness.Section6
