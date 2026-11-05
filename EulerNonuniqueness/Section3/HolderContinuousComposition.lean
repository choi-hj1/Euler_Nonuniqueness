import EulerNonuniqueness.Section3.HolderContinuousVectors
import EulerNonuniqueness.Section3.HolderFixedLabelComposition

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] holderContinuousRealSpace translationC1RealSpace

def holderSteklovLift (data : PeriodicHolderHalf) (member : data ∈ holderContinuousVectorSubmodule)
    (step : ℝ) : PeriodicC1HolderHalf :=
  let averaged := holderSteklovAverage data step
  let tangent := step⁻¹ • (holderPureLabelAction step data - data)
  PeriodicC1HolderHalf.ofFunctions averaged.val.1 tangent.val.1 averaged.val.1.continuous tangent.val.1.continuous
    ‖averaged‖ ‖tangent‖ ‖tangent‖
    (PeriodicHolderHalf.value_bound averaged) (PeriodicHolderHalf.value_bound tangent)
    (PeriodicHolderHalf.holder_bound tangent) (holderSteklovAverage_hasDerivAt data member step)
    (PeriodicHolderHalf.periodic averaged) (PeriodicHolderHalf.periodic tangent)

theorem holderSteklovLift_value (data : PeriodicHolderHalf) (member : data ∈ holderContinuousVectorSubmodule)
    (step label : ℝ) :
    (holderSteklovLift data member step).val.1 label = (holderSteklovAverage data step).val.1 label := rfl

theorem holderSteklovLift_valueHolder (data : PeriodicHolderHalf) (member : data ∈ holderContinuousVectorSubmodule)
    (step : ℝ) : c1ValueHolder (holderSteklovLift data member step) = holderSteklovAverage data step := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem PeriodicC1LabelMap.composeHolder_mem_continuousVector (labels : PeriodicC1LabelMap)
    (data : PeriodicHolderHalf) (member : data ∈ holderContinuousVectorSubmodule) :
    labels.composeHolderCLM data ∈ holderContinuousVectorSubmodule := by
  have limit := labels.composeHolderCLM.continuous.continuousAt.tendsto.comp (holderSteklovAverage_tendsto data member)
  apply holderContinuousVectorSubmodule_closed.mem_of_tendsto limit
  apply Filter.Eventually.of_forall
  intro step
  have identity : labels.composeHolderCLM (holderSteklovAverage data step) =
      c1ValueHolder (labels.compose (holderSteklovLift data member step)) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    rfl
  change labels.composeHolderCLM (holderSteklovAverage data step) ∈ holderContinuousVectorSubmodule
  rw [identity]
  exact c1ValueHolder_mem_holderContinuousVectorSubmodule _

end EulerNonuniqueness.Paper
