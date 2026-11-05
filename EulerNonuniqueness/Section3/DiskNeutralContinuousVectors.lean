import EulerNonuniqueness.Section3.DiskStationaryContinuousVectors
import EulerNonuniqueness.Section3.DiskRelabelNeutralPart

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance neutralContinuousC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourContinuousVectorSubmodule_product (first second : PeriodicC1HolderHalf)
    (firstMember : first ∈ contourContinuousVectorSubmodule)
    (secondMember : second ∈ contourContinuousVectorSubmodule) :
    c1Product first second ∈ contourContinuousVectorSubmodule := by
  have firstOrbit := continuous_contourLabelShiftCCLM first firstMember
  have secondOrbit := continuous_contourLabelShiftCCLM second secondMember
  have composition := c1Product_continuous.comp (firstOrbit.prodMk secondOrbit)
  apply contourContinuousVector_of_labelShift
  convert composition using 1
  funext offset
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value]
  change first.val.1 (label + offset) * second.val.1 (label + offset) =
    (contourLabelShiftCCLM offset first).val.1 label * (contourLabelShiftCCLM offset second).val.1 label
  rw [contourLabelShiftCCLM_value, contourLabelShiftCCLM_value]

theorem contourContinuousVectorSubmodule_conjugate (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    c1Conjugate data ∈ contourContinuousVectorSubmodule := by
  have orbit := continuous_contourLabelShiftCCLM data member
  have composition := c1ConjugateCLM.continuous.comp orbit
  apply contourContinuousVector_of_labelShift
  convert composition using 1
  funext offset
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value]
  change star (data.val.1 (label + offset)) = star ((contourLabelShiftCCLM offset data).val.1 label)
  rw [contourLabelShiftCCLM_value]

theorem diskNeutralCLM_mem_contourContinuousVectorSubmodule (increment : PeriodicC1HolderHalf)
    (member : increment ∈ contourContinuousVectorSubmodule) :
    diskNeutralCLM increment ∈ contourContinuousVectorSubmodule := by
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset increment) := member
  have composition := diskNeutralCLM.continuous.comp orbit
  apply contourContinuousVector_of_labelShift
  simpa only [Function.comp_def, normalizedContourShiftCLM_apply, diskNeutralCLM_normalized_shift] using composition

theorem diskRelabelNeutralCLM_mem_contourContinuousVectorSubmodule (increment : PeriodicC1HolderHalf)
    (member : increment ∈ contourContinuousVectorSubmodule) :
    diskRelabelNeutralCLM increment ∈ contourContinuousVectorSubmodule :=
  contourContinuousVectorSubmodule_product standardCircleBanach _ standardCircle_mem_contourContinuousVectorSubmodule
    (contourContinuousVectorSubmodule_constant_product Complex.I _
      (diskNeutralCLM_mem_contourContinuousVectorSubmodule increment member))

theorem diskStationaryNeutral_mem_contourContinuousVectorSubmodule (increment : PeriodicC1HolderHalf)
    (member : increment ∈ contourContinuousVectorSubmodule) :
    diskStationaryChart (diskRelabelNeutralCLM increment) ∈ contourContinuousVectorSubmodule :=
  diskStationaryChart_mem_contourContinuousVectorSubmodule _
    (diskRelabelNeutralCLM_mem_contourContinuousVectorSubmodule increment member)

end EulerNonuniqueness.Paper
