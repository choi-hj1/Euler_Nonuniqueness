import EulerNonuniqueness.Section8.RegularizedAdvection
import EulerNonuniqueness.General.SliceInjectionAdvection

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BoundedContinuousFunction

namespace EulerNonuniqueness.RegularizedFlowOn

variable {source : Vorticity} {integrable : Integrable source}
  {scale horizon : ℝ} {positive : 0 < scale}
  (flow : RegularizedFlowOn source integrable scale positive horizon)

theorem continuous_particleMap_on_time_subtype :
    Continuous (fun point : Icc 0 horizon × Plane => flow.particleMap point.1 point.2) := by
  have pathContinuous : Continuous (fun time : Icc 0 horizon => flow.displacement time) :=
    continuousOn_iff_continuous_restrict.mp flow.continuous
  exact continuous_snd.add (BoundedContinuousFunction.continuous_eval.comp
    ((pathContinuous.comp continuous_fst).prodMk continuous_snd))

theorem measurable_vorticity_on_time_subtype (sourceMeasurable : Measurable source) :
    Measurable (fun point : Icc 0 horizon × Plane => flow.vorticity point.1 point.2) :=
  measurable_slice_injectionAdvection flow.continuous_particleMap_on_time_subtype.measurable
    (fun time => flow.injective_particleMap time.property) sourceMeasurable

end EulerNonuniqueness.RegularizedFlowOn
