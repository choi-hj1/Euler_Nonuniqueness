import EulerNonuniqueness.General.ContinuousVectorSteklov
import EulerNonuniqueness.Section3.ContourContinuousFourierAverage

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] continuousFourierC1Group
  forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

def contourPureLabelAction (time : ℝ) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  (contourLabelShiftCCLM time).restrictScalars ℝ

theorem contourPureLabelAction_zero : contourPureLabelAction 0 = ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
  apply ContinuousLinearMap.ext
  intro data
  apply PeriodicC1HolderHalf.ext_value
  intro label
  simpa only [ContinuousLinearMap.id_apply, add_zero] using contourLabelShiftCCLM_value 0 data label

theorem contourPureLabelAction_add (first second : ℝ) (data : PeriodicC1HolderHalf) :
    contourPureLabelAction first (contourPureLabelAction second data) = contourPureLabelAction (first + second) data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (contourLabelShiftCCLM first (contourLabelShiftCCLM second data)).val.1 label =
    (contourLabelShiftCCLM (first + second) data).val.1 label
  rw [contourLabelShiftCCLM_value, contourLabelShiftCCLM_value, contourLabelShiftCCLM_value, add_assoc]

def contourSteklovAverage (data : PeriodicC1HolderHalf) (step : ℝ) : PeriodicC1HolderHalf :=
  EulerNonuniqueness.General.continuousVectorAverage contourPureLabelAction data step

theorem contourSteklovAverage_tendsto (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    Tendsto (contourSteklovAverage data) (𝓝[≠] (0 : ℝ)) (𝓝 data) := by
  apply EulerNonuniqueness.General.continuousVectorAverage_tendsto contourPureLabelAction contourPureLabelAction_zero data
  exact continuous_contourLabelShiftCCLM data member

theorem contourSteklovAverage_tangent_witness (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) (step : ℝ) :
    ∃ tangent : PeriodicC1HolderHalf, ∀ label,
      tangent.val.1 label = (contourSteklovAverage data step).val.2.val.1 label := by
  let tangent := step⁻¹ • (contourPureLabelAction step data - data)
  have pureMember : data ∈ EulerNonuniqueness.General.continuousVectorSubmodule contourPureLabelAction :=
    continuous_contourLabelShiftCCLM data member
  have derivative := EulerNonuniqueness.General.continuousVectorAverage_orbit_hasDerivAt
    contourPureLabelAction contourPureLabelAction_add data pureMember step 0
  have actual : HasDerivAt (fun time => contourPureLabelAction time (contourSteklovAverage data step)) tangent 0 := by
    simpa only [zero_add, contourPureLabelAction_zero, ContinuousLinearMap.id_apply] using derivative
  refine ⟨tangent, fun label => ?_⟩
  have evaluated := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := ℂ) 0
    (contourLabelEvaluation label).hasFDerivAt actual
  have shifted : HasDerivAt (fun time => (contourSteklovAverage data step).val.1 (label + time))
      ((contourSteklovAverage data step).val.2.val.1 label) 0 := by
    simpa only [Function.comp_def, one_smul] using
      (PeriodicC1HolderHalf.hasDerivAt (contourSteklovAverage data step) label).scomp_of_eq 0
        ((hasDerivAt_id (0 : ℝ)).const_add label) (by simp)
  have identity : (fun time => contourLabelEvaluation label
      (contourPureLabelAction time (contourSteklovAverage data step))) =
      fun time => (contourSteklovAverage data step).val.1 (label + time) := by
    funext time
    exact contourLabelShiftCCLM_value time _ label
  change HasDerivAt (fun time => contourLabelEvaluation label
    (contourPureLabelAction time (contourSteklovAverage data step))) _ 0 at evaluated
  rw [identity] at evaluated
  simpa only [one_smul] using evaluated.unique shifted

end EulerNonuniqueness.Paper
