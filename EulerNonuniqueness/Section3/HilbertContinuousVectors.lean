import EulerNonuniqueness.Section3.ContourAngularSelection
import EulerNonuniqueness.Section3.ContourContinuousGauge
import EulerNonuniqueness.Section3.PeriodicHilbertSpectral
import EulerNonuniqueness.Section3.DiskAreaMeanProjection

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance hilbertContinuousC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

private theorem complex_smul_mem (scalar : ℂ) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) : scalar • data ∈ contourContinuousVectorSubmodule := by
  have identity : scalar • data = c1Product (c1Constant scalar) data := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  rw [identity]
  exact contourContinuousVectorSubmodule_constant_product scalar data member

theorem periodicHilbertC1_labelShift (offset : ℝ) (data : PeriodicC1HolderHalf) :
    periodicHilbertC1 (contourLabelShiftCCLM offset data) =
      contourLabelShiftCCLM offset (periodicHilbertC1 data) := by
  have embedding : c1ValueHolder (contourLabelShiftCCLM offset data) =
      holderLabelShift offset (c1ValueHolder data) := by
    apply PeriodicHolderHalf.ext_value
    intro label
    exact contourLabelShiftCCLM_value offset data label
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value, periodicHilbertC1_value, periodicHilbertC1_value,
    embedding, periodicHilbertCLM_shift, holderLabelShift_value]

theorem contourContinuousVectorSubmodule_hilbert (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    periodicHilbertC1 data ∈ contourContinuousVectorSubmodule := by
  have orbit := continuous_contourLabelShiftCCLM data member
  have composition : Continuous (fun offset => periodicHilbertC1 (contourLabelShiftCCLM offset data)) := by
    change Continuous (fun offset => periodicHilbertC1CLM (contourLabelShiftCCLM offset data))
    exact periodicHilbertC1CLM.continuous.comp orbit
  apply contourContinuousVector_of_labelShift
  simpa only [periodicHilbertC1_labelShift] using composition

theorem contourContinuousVectorSubmodule_positive_projection (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    periodicHilbertPositiveProjection data ∈ contourContinuousVectorSubmodule := by
  have meanMember : periodicMeanProjectionCCLM data ∈ contourContinuousVectorSubmodule := by
    rw [periodicMeanProjectionCCLM_eq_constant]
    exact contourContinuousVectorSubmodule_constant _
  rw [periodicHilbertPositiveProjection_apply]
  apply complex_smul_mem
  exact contourContinuousVectorSubmodule.add_mem
    (contourContinuousVectorSubmodule.sub_mem member meanMember)
    (complex_smul_mem Complex.I _ (contourContinuousVectorSubmodule_hilbert data member))

theorem diskRadialPart_labelShift (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    contourLabelShiftCCLM offset (diskRadialPart direction) =
      diskRadialPart (normalizedContourShift offset direction) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value, diskRadialPart_value, diskRadialPart_value,
    normalizedContourShift_value, standardCircle_add, star_mul, standardCircle_star_eq_inv]
  congr 2
  ring

theorem contourContinuousVectorSubmodule_radial (direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule) :
    diskRadialPart direction ∈ contourContinuousVectorSubmodule := by
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset direction) := member
  have composition : Continuous (fun offset => diskRadialCLM (normalizedContourShiftCLM offset direction)) :=
    diskRadialCLM.continuous.comp orbit
  apply contourContinuousVector_of_labelShift
  simpa only [diskRadialPart_labelShift, diskRadialCLM_apply, normalizedContourShiftCLM_apply] using composition

end

end EulerNonuniqueness.Paper
