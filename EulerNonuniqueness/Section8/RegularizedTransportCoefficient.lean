import EulerNonuniqueness.Section8.RegularizedAdvectionMeasurability
import EulerNonuniqueness.Section8.RegularizedCharacteristic

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction ContDiff

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem continuous_regularizedVelocity_on_time_subtype (nonnegative : 0 ≤ horizon) :
    Continuous (fun point : Icc 0 horizon × Plane =>
      regularizedBiotSavart scale (flow.vorticity point.1) point.2) := by
  have pathContinuous : Continuous (fun time : Icc 0 horizon => flow.displacement time) :=
    continuousOn_iff_continuous_restrict.mp flow.continuous
  have lagrangianContinuous := (continuous_lagrangianVelocity integrable
    (lipschitz_regularizedBiotSavartKernel positive).continuous
    (bound := regularizedKernelNormBound positive)
    (fun position => norm_regularizedBiotSavartKernel_le positive position)).comp
      ((pathContinuous.comp continuous_fst).prodMk continuous_snd)
  apply lagrangianContinuous.congr
  intro point
  exact (flow.regularizedBiotSavart_vorticity nonnegative point.1.property point.2).symm

theorem continuous_transportCoefficient_on_time_subtype (nonnegative : 0 ≤ horizon)
    {test : ℝ × Plane → ℝ} (smooth : ContDiff ℝ 1 test) :
    Continuous (fun point : Icc 0 horizon × Plane =>
      timeDerivative test (point.1, point.2) + spatialDerivative test (point.1, point.2)
        (regularizedBiotSavart scale (flow.vorticity point.1) point.2)) := by
  have pointContinuous : Continuous (fun point : Icc 0 horizon × Plane => ((point.1 : ℝ), point.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have derivativeContinuous := (smooth.continuous_fderiv le_rfl).comp pointContinuous
  exact (derivativeContinuous.clm_apply continuous_const).add
    (derivativeContinuous.clm_apply (continuous_const.prodMk
      (flow.continuous_regularizedVelocity_on_time_subtype nonnegative)))

theorem norm_regularizedVelocity_le_crude (nonnegative : 0 ≤ horizon)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) (position : Plane) :
    ‖regularizedBiotSavart scale (flow.vorticity time) position‖ ≤
      regularizedKernelNormBound positive * sourceL1Mass source := by
  rw [flow.regularizedBiotSavart_vorticity nonnegative inside position]
  exact norm_lagrangianVelocity_le integrable (bound := regularizedKernelNormBound positive)
    (fun point => norm_regularizedBiotSavartKernel_le positive point) (flow.displacement time) position

end EulerNonuniqueness.RegularizedFlowOn
