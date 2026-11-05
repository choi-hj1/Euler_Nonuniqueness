import EulerNonuniqueness.Section6.CoMovingInversePowerKernel
import EulerNonuniqueness.Section6.VorticitySelfInteraction

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

def inverseSquareVorticityWeight (vorticity : Vorticity) (center position : ℂ) : ℝ :=
  |vorticity position| * ‖center - position‖⁻¹ ^ 2

theorem integrable_inverseSquareVorticityWeight {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) :
    Integrable (inverseSquareVorticityWeight vorticity center) := by
  have radialMeasurable : Measurable (fun position : ℂ => ‖center - position‖⁻¹ ^ 2) := by fun_prop
  apply (integrable.norm.const_mul (distance⁻¹ ^ 2)).mono'
    (integrable.aestronglyMeasurable.norm.mul radialMeasurable.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun position => by
    by_cases zero : vorticity position = 0
    · simp [inverseSquareVorticityWeight, zero]
    have lower := separated position (Function.mem_support.mpr zero)
    have inverseBound := inv_anti₀ positive lower
    change ‖|vorticity position| * ‖center - position‖⁻¹ ^ 2‖ ≤ distance⁻¹ ^ 2 * |vorticity position|
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)), mul_comm (distance⁻¹ ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr (positive.trans_le lower).le) inverseBound 2) (abs_nonneg _)

theorem coMovingInversePowerKernel_weighted_bound {vorticity : Vorticity} (center : ℂ)
    {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖)
    (power : ℕ) (pair : ℂ × ℂ) :
    ‖vorticity pair.1 • (vorticity pair.2 • coMovingInversePowerKernel (power + 3)
      (center - pair.1) (center - pair.2))‖ ≤
      (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) *
        (inverseSquareVorticityWeight vorticity center pair.1 * inverseSquareVorticityWeight vorticity center pair.2) := by
  by_cases firstZero : vorticity pair.1 = 0
  · simp [firstZero, inverseSquareVorticityWeight]
  by_cases secondZero : vorticity pair.2 = 0
  · simp [secondZero, inverseSquareVorticityWeight]
  have estimate := coMovingInversePowerKernel_bound positive
    (separated pair.1 (Function.mem_support.mpr firstZero))
    (separated pair.2 (Function.mem_support.mpr secondZero)) power
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left estimate (abs_nonneg _))
    (abs_nonneg _)).trans_eq (by dsimp only [inverseSquareVorticityWeight]; ring)

theorem integrable_weighted_coMovingInversePowerKernel {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    Integrable (fun pair : ℂ × ℂ => vorticity pair.1 •
      (vorticity pair.2 • coMovingInversePowerKernel (power + 3) (center - pair.1) (center - pair.2)))
      (volume.prod volume) := by
  have weight := integrable_inverseSquareVorticityWeight integrable center positive separated
  have kernelMeasurable : Measurable (fun pair : ℂ × ℂ =>
      coMovingInversePowerKernel (power + 3) (center - pair.1) (center - pair.2)) := by
    unfold coMovingInversePowerKernel
    fun_prop
  apply ((weight.mul_prod weight).const_mul
    (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power)).mono'
      (integrable.aestronglyMeasurable.fst.smul (integrable.aestronglyMeasurable.snd.smul
        kernelMeasurable.aestronglyMeasurable))
  exact Filter.Eventually.of_forall (coMovingInversePowerKernel_weighted_bound center positive separated power)

theorem norm_integral_weighted_coMovingInversePowerKernel {vorticity : Vorticity}
    (integrable : Integrable vorticity) (center : ℂ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    ‖∫ first : ℂ, ∫ second : ℂ, vorticity first •
      (vorticity second • coMovingInversePowerKernel (power + 3) (center - first) (center - second))‖ ≤
      (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power) *
        (∫ position, inverseSquareVorticityWeight vorticity center position) ^ 2 := by
  have joint := integrable_weighted_coMovingInversePowerKernel integrable center positive separated power
  have weight := integrable_inverseSquareVorticityWeight integrable center positive separated
  rw [← integral_prod _ joint]
  have estimate := norm_integral_le_of_norm_le
    ((weight.mul_prod weight).const_mul (((power + 3 : ℝ) * 2 ^ (power + 2) + 10) * distance⁻¹ ^ power))
    (Filter.Eventually.of_forall (coMovingInversePowerKernel_weighted_bound center positive separated power))
  rw [integral_const_mul, integral_prod_mul, ← pow_two] at estimate
  exact estimate

end EulerNonuniqueness.Section6
