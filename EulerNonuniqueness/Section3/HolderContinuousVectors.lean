import EulerNonuniqueness.General.ContinuousVectorSteklov
import EulerNonuniqueness.Section3.HolderTranslationContinuity

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance holderContinuousRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph

def holderPureLabelAction (time : ℝ) : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
  LinearMap.mkContinuous
    { toFun := holderLabelShift time
      map_add' := fun first second => by
        apply PeriodicHolderHalf.ext_value
        intro label
        rfl
      map_smul' := fun scalar data => by
        apply PeriodicHolderHalf.ext_value
        intro label
        rfl }
    1 (fun data => by simpa only [one_mul] using holderLabelShift_norm_le time data)

theorem holderPureLabelAction_value (time : ℝ) (data : PeriodicHolderHalf) (label : ℝ) :
    (holderPureLabelAction time data).val.1 label = data.val.1 (label + time) := rfl

theorem holderPureLabelAction_zero : holderPureLabelAction 0 = ContinuousLinearMap.id ℝ PeriodicHolderHalf := by
  apply ContinuousLinearMap.ext
  intro data
  apply PeriodicHolderHalf.ext_value
  intro label
  change data.val.1 (label + 0) = data.val.1 label
  rw [add_zero]

theorem holderPureLabelAction_add (first second : ℝ) (data : PeriodicHolderHalf) :
    holderPureLabelAction first (holderPureLabelAction second data) = holderPureLabelAction (first + second) data := by
  apply PeriodicHolderHalf.ext_value
  intro label
  change data.val.1 ((label + first) + second) = data.val.1 (label + (first + second))
  rw [add_assoc]

def holderContinuousVectorSubmodule : Submodule ℝ PeriodicHolderHalf :=
  EulerNonuniqueness.General.continuousVectorSubmodule holderPureLabelAction

theorem holderContinuousVectorSubmodule_closed : IsClosed (holderContinuousVectorSubmodule : Set PeriodicHolderHalf) := by
  exact EulerNonuniqueness.General.continuousVectorSubmodule_closed holderPureLabelAction holderLabelShift_norm_le

theorem c1ValueHolder_mem_holderContinuousVectorSubmodule (data : PeriodicC1HolderHalf) :
    c1ValueHolder data ∈ holderContinuousVectorSubmodule := continuous_c1ValueHolder_shift data

def holderLabelEvaluationRealCLM (label : ℝ) : PeriodicHolderHalf →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun data => data.val.1 label
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    1 (fun data => by simpa only [one_mul] using PeriodicHolderHalf.value_bound data label)

def holderSteklovAverage (data : PeriodicHolderHalf) (step : ℝ) : PeriodicHolderHalf :=
  EulerNonuniqueness.General.continuousVectorAverage holderPureLabelAction data step

theorem holderSteklovAverage_tendsto (data : PeriodicHolderHalf)
    (member : data ∈ holderContinuousVectorSubmodule) :
    Tendsto (holderSteklovAverage data) (𝓝[≠] (0 : ℝ)) (𝓝 data) :=
  EulerNonuniqueness.General.continuousVectorAverage_tendsto holderPureLabelAction holderPureLabelAction_zero data member

theorem holderSteklovAverage_hasDerivAt (data : PeriodicHolderHalf)
    (member : data ∈ holderContinuousVectorSubmodule) (step label : ℝ) :
    HasDerivAt (holderSteklovAverage data step).val.1
      ((step⁻¹ • (holderPureLabelAction step data - data)).val.1 label) label := by
  have derivative := EulerNonuniqueness.General.continuousVectorAverage_orbit_hasDerivAt
    holderPureLabelAction holderPureLabelAction_add data member step label
  have evaluated := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicHolderHalf) (E := ℂ) label
    (holderLabelEvaluationRealCLM 0).hasFDerivAt derivative
  have identity : (fun time => holderLabelEvaluationRealCLM 0 (holderPureLabelAction time (holderSteklovAverage data step))) =
      (holderSteklovAverage data step).val.1 := by
    funext time
    change (holderSteklovAverage data step).val.1 (0 + time) = _
    rw [zero_add]
  change HasDerivAt (fun time => holderLabelEvaluationRealCLM 0 (holderPureLabelAction time (holderSteklovAverage data step))) _ label at evaluated
  rw [identity] at evaluated
  convert evaluated using 1
  change step⁻¹ • (data.val.1 (label + step) - data.val.1 label) =
    step⁻¹ • (data.val.1 (0 + (label + step)) - data.val.1 (0 + label))
  rw [zero_add, zero_add]

end EulerNonuniqueness.Paper
