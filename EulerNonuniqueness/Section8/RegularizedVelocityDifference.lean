import EulerNonuniqueness.Section8.RegularizedKernelCutoff
import EulerNonuniqueness.General.ConvolutionBounds

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

def regularizedBiotSavart (scale : ℝ) (vorticity : Vorticity) : Velocity :=
  fun position => ∫ source, vorticity source • regularizedBiotSavartKernel scale (position - source)

theorem integrable_regularizedBiotSavart_integrand {scale : ℝ} (positive : 0 < scale)
    {vorticity : Vorticity} (integrable : Integrable vorticity) (position : Plane) :
    Integrable (fun source => vorticity source • regularizedBiotSavartKernel scale (position - source)) :=
  integrable_convolution_smul_of_bounded integrable
    (contDiff_regularizedBiotSavartKernel positive).continuous.aestronglyMeasurable
    (norm_regularizedBiotSavartKernel_le positive) position

theorem regularizedKernelDifference_convolution_bound {scale : ℝ} (positive : 0 < scale)
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume) (position : Plane) :
    Integrable (fun source => vorticity source •
      (regularizedBiotSavartKernel scale (position - source) - biotSavartKernel (position - source))) ∧
      ‖∫ source, vorticity source •
        (regularizedBiotSavartKernel scale (position - source) - biotSavartKernel (position - source))‖ ≤
        (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
          (eLpNorm (nearRegularizedKernelDifference scale) (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
            (∫ source, ‖vorticity source‖) * (scale ^ 2 / (2 * Real.pi)) := by
  have nearMember := nearRegularizedKernelDifference_memLp positive (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)
  have nearIntegrable := integrable_convolution_smul_of_memLp holderConjugate_four_fourThirds
    membership nearMember position
  have farIntegrable := integrable_convolution_smul_of_bounded integrable
    (measurable_farRegularizedKernelDifference positive).aestronglyMeasurable
    (norm_farRegularizedKernelDifference_le positive) position
  have split : (fun source => vorticity source •
      (regularizedBiotSavartKernel scale (position - source) - biotSavartKernel (position - source))) =
      fun source => vorticity source • nearRegularizedKernelDifference scale (position - source) +
        vorticity source • farRegularizedKernelDifference scale (position - source) := by
    funext source
    have identity := congrFun (near_add_far_regularizedKernelDifference scale) (position - source)
    change nearRegularizedKernelDifference scale (position - source) +
      farRegularizedKernelDifference scale (position - source) =
        regularizedBiotSavartKernel scale (position - source) - biotSavartKernel (position - source) at identity
    rw [← identity, smul_add]
  rw [split]
  refine ⟨nearIntegrable.add farIntegrable, ?_⟩
  rw [integral_add nearIntegrable farIntegrable]
  exact (norm_add_le _ _).trans (add_le_add
    (norm_convolution_smul_le_eLpNorm holderConjugate_four_fourThirds membership nearMember position)
    (norm_convolution_smul_le_of_bounded integrable (norm_farRegularizedKernelDifference_le positive) position))

theorem integrable_biotSavart_integrand_of_L1_L4 {vorticity : Vorticity}
    (integrable : Integrable vorticity) (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (position : Plane) :
    Integrable (fun source => vorticity source • biotSavartKernel (position - source)) := by
  have regularized := integrable_regularizedBiotSavart_integrand (by norm_num : (0 : ℝ) < 1) integrable position
  have difference := (regularizedKernelDifference_convolution_bound (by norm_num : (0 : ℝ) < 1)
    integrable membership position).1
  apply (regularized.sub difference).congr
  exact Filter.Eventually.of_forall fun source => by
    simp only [Pi.sub_apply]
    rw [smul_sub]
    abel

theorem norm_regularizedBiotSavart_sub_le {scale : ℝ} (positive : 0 < scale)
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume) (position : Plane) :
    ‖regularizedBiotSavart scale vorticity position - biotSavart vorticity position‖ ≤
      (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
        (eLpNorm (nearRegularizedKernelDifference scale) (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
          (∫ source, ‖vorticity source‖) * (scale ^ 2 / (2 * Real.pi)) := by
  rw [regularizedBiotSavart, biotSavart,
    ← integral_sub (integrable_regularizedBiotSavart_integrand positive integrable position)
      (integrable_biotSavart_integrand_of_L1_L4 integrable membership position)]
  simpa only [smul_sub] using (regularizedKernelDifference_convolution_bound positive integrable membership position).2

end EulerNonuniqueness
