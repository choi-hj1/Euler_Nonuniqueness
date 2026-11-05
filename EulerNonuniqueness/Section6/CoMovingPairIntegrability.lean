import EulerNonuniqueness.Section6.CoMovingBiotSavartSymmetry

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

def coMovingVorticityPair (vorticity : Vorticity) (center : ℂ) (power : ℕ) (pair : ℂ × ℂ) : ℂ :=
  vorticity pair.1 • (vorticity pair.2 •
    (star (biotSavartKernel (center - pair.2) - biotSavartKernel (pair.1 - pair.2)) *
      (star (center - pair.1))⁻¹ ^ power))

theorem integrable_coMovingVorticityPair {vorticity : Vorticity}
    (integrable : Integrable vorticity) {radius bound distance : ℝ}
    (supported : Function.support vorticity ⊆ Metric.closedBall 0 radius)
    (bounded : ∀ position, |vorticity position| ≤ bound)
    (center : ℂ) (positive : 0 < distance)
    (separated : ∀ position ∈ Function.support vorticity, distance ≤ ‖center - position‖) (power : ℕ) :
    Integrable (coMovingVorticityPair vorticity center power) (volume.prod volume) := by
  have joint := integrable_vorticity_pair_kernel integrable supported bounded
  have product := integrable.norm.mul_prod integrable.norm
  let majorant := fun pair : ℂ × ℂ =>
    (distance⁻¹ ^ power / (2 * Real.pi * distance)) * (|vorticity pair.1| * |vorticity pair.2|) +
      distance⁻¹ ^ power * ‖vorticity pair.1 • (vorticity pair.2 • biotSavartKernel (pair.1 - pair.2))‖
  have majorantIntegrable : Integrable majorant (volume.prod volume) :=
    (product.const_mul _).add (joint.norm.const_mul _)
  have kernelMeasurable : Measurable (fun pair : ℂ × ℂ =>
      star (biotSavartKernel (center - pair.2) - biotSavartKernel (pair.1 - pair.2)) *
        (star (center - pair.1))⁻¹ ^ power) := by
    apply Measurable.mul
    · have conjugateMeasurable : Measurable (star : ℂ → ℂ) := by fun_prop
      exact conjugateMeasurable.comp ((measurable_biotSavartKernel.comp (measurable_const.sub measurable_snd)).sub
        (measurable_biotSavartKernel.comp (measurable_fst.sub measurable_snd)))
    · fun_prop
  apply majorantIntegrable.mono'
    (integrable.aestronglyMeasurable.fst.smul
      (integrable.aestronglyMeasurable.snd.smul kernelMeasurable.aestronglyMeasurable))
  exact Filter.Eventually.of_forall fun pair => by
    by_cases firstZero : vorticity pair.1 = 0
    · simp [coMovingVorticityPair, majorant, firstZero]
    by_cases secondZero : vorticity pair.2 = 0
    · simp [coMovingVorticityPair, majorant, secondZero]
    have firstGap := separated pair.1 (Function.mem_support.mpr firstZero)
    have secondGap := separated pair.2 (Function.mem_support.mpr secondZero)
    have inverseBound := inv_anti₀ positive firstGap
    have powerBound : ‖(star (center - pair.1))⁻¹ ^ power‖ ≤ distance⁻¹ ^ power := by
      simp only [norm_pow, norm_inv, norm_star]
      exact pow_le_pow_left₀ (inv_nonneg.mpr (positive.trans_le firstGap).le) inverseBound power
    have centerKernelBound : ‖biotSavartKernel (center - pair.2)‖ ≤ 1 / (2 * Real.pi * distance) := by
      rw [norm_biotSavartKernel]
      exact one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left secondGap (by positivity))
    have differenceBound : ‖star (biotSavartKernel (center - pair.2) - biotSavartKernel (pair.1 - pair.2))‖ ≤
        1 / (2 * Real.pi * distance) + ‖biotSavartKernel (pair.1 - pair.2)‖ := by
      rw [norm_star]
      exact (norm_sub_le _ _).trans (add_le_add_right centerKernelBound _)
    have productBound := mul_le_mul differenceBound powerBound (norm_nonneg _)
      (by positivity : 0 ≤ 1 / (2 * Real.pi * distance) + ‖biotSavartKernel (pair.1 - pair.2)‖)
    have scaled := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left productBound (abs_nonneg (vorticity pair.2)))
      (abs_nonneg (vorticity pair.1))
    simpa only [coMovingVorticityPair, majorant, norm_smul, Real.norm_eq_abs, norm_mul] using
      scaled.trans_eq (by ring)

end EulerNonuniqueness.Section6
