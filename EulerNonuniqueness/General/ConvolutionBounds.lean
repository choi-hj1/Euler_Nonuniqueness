import EulerNonuniqueness.General.ConvolutionContinuity

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem integrable_convolution_smul_of_memLp {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {exponent conjugate : ℝ} {weight : ℂ → ℝ} {kernel : ℂ → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) volume)
    (kernelMember : MemLp kernel (ENNReal.ofReal conjugate) volume) (position : ℂ) :
    Integrable (fun source => weight source • kernel (position - source)) := by
  letI : ENNReal.HolderTriple (ENNReal.ofReal exponent) (ENNReal.ofReal conjugate) 1 :=
    by simpa using conjugacy.ennrealOfReal
  exact memLp_one_iff_integrable.mp
    ((kernelMember.comp_measurePreserving (volume.measurePreserving_sub_left position)).smul weightMember)

theorem norm_convolution_smul_le_eLpNorm {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {exponent conjugate : ℝ} {weight : ℂ → ℝ} {kernel : ℂ → Value}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) volume)
    (kernelMember : MemLp kernel (ENNReal.ofReal conjugate) volume) (position : ℂ) :
    ‖∫ source, weight source • kernel (position - source)‖ ≤
      (eLpNorm weight (ENNReal.ofReal exponent) volume).toReal *
        (eLpNorm kernel (ENNReal.ofReal conjugate) volume).toReal := by
  have estimate := norm_integral_smul_le_eLpNorm conjugacy weightMember
    (kernelMember.comp_measurePreserving (volume.measurePreserving_sub_left position))
  have normEquality := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal conjugate)
    kernelMember.aestronglyMeasurable (volume.measurePreserving_sub_left position)
  rw [normEquality] at estimate
  simpa only [Function.comp_apply] using estimate

theorem integrable_convolution_smul_of_bounded {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {weight : ℂ → ℝ} {kernel : ℂ → Value} {bound : ℝ}
    (integrable : Integrable weight) (measurable : AEStronglyMeasurable kernel volume)
    (bounded : ∀ position, ‖kernel position‖ ≤ bound) (position : ℂ) :
    Integrable (fun source => weight source • kernel (position - source)) := by
  apply (integrable.norm.mul_const bound).mono'
    (integrable.aestronglyMeasurable.smul
      (measurable.comp_measurePreserving (volume.measurePreserving_sub_left position)))
  exact Filter.Eventually.of_forall fun source => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)

theorem norm_convolution_smul_le_of_bounded {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {weight : ℂ → ℝ} {kernel : ℂ → Value} {bound : ℝ}
    (integrable : Integrable weight) (bounded : ∀ position, ‖kernel position‖ ≤ bound) (position : ℂ) :
    ‖∫ source, weight source • kernel (position - source)‖ ≤
      (∫ source, ‖weight source‖) * bound := by
  rw [← integral_mul_const]
  apply norm_integral_le_of_norm_le (integrable.norm.mul_const bound)
  exact Filter.Eventually.of_forall fun source => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (bounded _) (norm_nonneg _)

end MeasureTheory
