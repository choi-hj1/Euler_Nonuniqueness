import EulerNonuniqueness.Section8.BiotSavart

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem measurable_kernel_convolution {Parameter : Type*} [MeasurableSpace Parameter]
    {vorticity : Parameter → Vorticity} (sourceMeasurable : Measurable (Function.uncurry vorticity))
    {kernel : Velocity} (kernelMeasurable : Measurable kernel) :
    Measurable (fun point : Parameter × Plane =>
      ∫ source, vorticity point.1 source • kernel (point.2 - source)) := by
  have source : Measurable (fun point : (Parameter × Plane) × Plane => vorticity point.1.1 point.2) :=
    sourceMeasurable.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have displacement : Measurable (fun point : (Parameter × Plane) × Plane => point.1.2 - point.2) :=
    (measurable_snd.comp measurable_fst).sub measurable_snd
  exact (source.smul (kernelMeasurable.comp displacement)).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_biotSavart_of_measurable_vorticity {Parameter : Type*} [MeasurableSpace Parameter]
    {vorticity : Parameter → Vorticity} (sourceMeasurable : Measurable (Function.uncurry vorticity)) :
    Measurable (fun point : Parameter × Plane => biotSavart (vorticity point.1) point.2) :=
  measurable_kernel_convolution sourceMeasurable measurable_biotSavartKernel

end EulerNonuniqueness
