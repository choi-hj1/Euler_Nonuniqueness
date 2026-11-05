import EulerNonuniqueness.Section8.DominatedBiotSavartBound
import EulerNonuniqueness.Section8.RegularizedVelocityDifference

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

theorem norm_biotSavart_le_L1_L4 {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume) (position : Plane) :
    ‖biotSavart vorticity position‖ ≤
      (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
        (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
          (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
            (∫ source, ‖vorticity source‖) * (1 / (2 * Real.pi)) :=
  (convolution_bound_of_biotSavart_domination measurable_biotSavartKernel.aestronglyMeasurable
    (fun _ => le_rfl) integrable membership position).2

theorem norm_regularizedBiotSavart_le_L1_L4 {scale : ℝ} (positive : 0 < scale)
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume) (position : Plane) :
    ‖regularizedBiotSavart scale vorticity position‖ ≤
      (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
        (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
          (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
            (∫ source, ‖vorticity source‖) * (1 / (2 * Real.pi)) :=
  (convolution_bound_of_biotSavart_domination
    (contDiff_regularizedBiotSavartKernel positive).continuous.aestronglyMeasurable
    (norm_regularizedBiotSavartKernel_le_kernel positive) integrable membership position).2

theorem norm_regularizedBiotSavart_le_uniform {scale : ℝ} (positive : 0 < scale)
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {oneBound fourBound : ℝ}
    (oneBounded : (∫ source, ‖vorticity source‖) ≤ oneBound)
    (fourBounded : (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal ≤ fourBound) (position : Plane) :
    ‖regularizedBiotSavart scale vorticity position‖ ≤
      fourBound * (eLpNorm ((Metric.ball (0 : Plane) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal + oneBound * (1 / (2 * Real.pi)) :=
  (norm_regularizedBiotSavart_le_L1_L4 positive integrable membership position).trans
    (add_le_add (mul_le_mul_of_nonneg_right fourBounded ENNReal.toReal_nonneg)
      (mul_le_mul_of_nonneg_right oneBounded (by positivity)))

end EulerNonuniqueness
