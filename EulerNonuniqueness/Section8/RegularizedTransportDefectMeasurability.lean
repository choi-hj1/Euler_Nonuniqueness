import EulerNonuniqueness.Section8.RegularizedDefectBound
import EulerNonuniqueness.Section8.MeasurableKernelConvolution
import EulerNonuniqueness.Section8.RegularizedTransportIntegrability

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

def regularizedTransportDefect {source : Vorticity} (integrable : Integrable source)
    {horizon : ℝ} (nonnegative : 0 ≤ horizon) (test : ℝ × Plane → ℝ) (index : ℕ)
    (point : ℝ × Plane) : ℝ :=
  regularizedApproximation integrable nonnegative index point.1 point.2 * spatialDerivative test point
    (biotSavart (regularizedApproximation integrable nonnegative index point.1) point.2 -
      regularizedBiotSavart (regularizationScale index)
        (regularizedApproximation integrable nonnegative index point.1) point.2)

theorem aestronglyMeasurable_regularizedTransportDefect {source : Vorticity}
    (integrable : Integrable source) {horizon : ℝ} (nonnegative : 0 ≤ horizon)
    (sourceMeasurable : Measurable source) {test : ℝ × Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (index : ℕ) :
    AEStronglyMeasurable (regularizedTransportDefect integrable nonnegative test index) (spacetimeMeasure horizon) := by
  let flow := regularizedApproximationFlow integrable nonnegative index
  have sliceMeasurable := flow.measurable_vorticity_on_time_subtype sourceMeasurable
  have sourceMeasurable' := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => flow.vorticity point.1 point.2) sliceMeasurable
  have biotSavartMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => biotSavart (flow.vorticity point.1) point.2)
    (measurable_biotSavart_of_measurable_vorticity
      (Parameter := Icc 0 horizon) (vorticity := fun time : Icc 0 horizon => flow.vorticity time) sliceMeasurable)
  have regularizedMeasurable := aestronglyMeasurable_spacetime_of_measurable_Icc nonnegative
    (field := fun point : ℝ × Plane => regularizedBiotSavart (regularizationScale index) (flow.vorticity point.1) point.2)
    (flow.continuous_regularizedVelocity_on_time_subtype nonnegative).measurable
  have derivativeMeasurable := (smooth.continuous_fderiv (by simp)).aestronglyMeasurable
    (μ := spacetimeMeasure horizon)
  have spatialMeasurable : AEStronglyMeasurable (fun point : ℝ × Plane => spatialDerivative test point
      (biotSavart (flow.vorticity point.1) point.2 -
        regularizedBiotSavart (regularizationScale index) (flow.vorticity point.1) point.2)) (spacetimeMeasure horizon) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivativeMeasurable.prodMk (aestronglyMeasurable_const.prodMk (biotSavartMeasurable.sub regularizedMeasurable)))
  exact sourceMeasurable'.mul spatialMeasurable

end EulerNonuniqueness
