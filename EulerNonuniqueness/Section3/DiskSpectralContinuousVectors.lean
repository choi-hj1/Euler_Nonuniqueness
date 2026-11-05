import EulerNonuniqueness.Section3.DiskChartedShiftEquivariance
import EulerNonuniqueness.Section3.DiskSpectralTubularInverse
import EulerNonuniqueness.General.CubicSpectralIntertwinerEquivariance
import EulerNonuniqueness.General.SpectralTubularEquivariance

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance spectralContinuousC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskRelabelNeutralCLM_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    diskRelabelNeutralCLM (normalizedContourShift offset increment) =
      normalizedContourShift offset (diskRelabelNeutralCLM increment) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [normalizedContourShift_value]
  change standardCircle label * (Complex.I * (diskNeutralCLM (normalizedContourShift offset increment)).val.1 label) =
    (standardCircle offset)⁻¹ * (standardCircle (label + offset) * (Complex.I * (diskNeutralCLM increment).val.1 (label + offset)))
  rw [diskNeutralCLM_normalized_shift, contourLabelShiftCCLM_value, standardCircle_add]
  have nonzero : standardCircle offset ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  field_simp
  <;> ring

theorem diskChartedNeutralOperator_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    (diskChartedNeutralOperator (normalizedContourShift offset increment)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (diskChartedNeutralOperator increment) := by
  unfold diskChartedNeutralOperator
  rw [diskRelabelNeutralCLM_normalized_shift]
  exact diskChartedEulerField_derivative_normalized_shift offset _

theorem diskRotatingDerivative_normalized_shift (offset : ℝ) :
    diskRotatingDerivative.comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp diskRotatingDerivative := by
  have actual := diskChartedEulerField_derivative_normalized_shift offset 0
  have zeroIdentity : normalizedContourShift offset (0 : PeriodicC1HolderHalf) = 0 :=
    map_zero (normalizedContourShiftCLM offset)
  simpa only [zeroIdentity, diskChartedEulerField_fderiv_zero] using actual

theorem diskChartedSpectralCoordinates_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    (diskChartedSpectralCoordinates (normalizedContourShift offset increment)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (diskChartedSpectralCoordinates increment) := by
  unfold diskChartedSpectralCoordinates
  with_reducible
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_equivariant (normalizedContourShiftCLM offset)
      (diskChartedNeutralOperator (normalizedContourShift offset increment)) (diskChartedNeutralOperator increment)
      diskRotatingDerivative (diskChartedNeutralOperator_normalized_shift offset increment)
      (diskRotatingDerivative_normalized_shift offset)

theorem diskSpectralTubularChart_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    diskSpectralTubularChart (normalizedContourShift offset increment) =
      normalizedContourShift offset (diskSpectralTubularChart increment) := by
  unfold diskSpectralTubularChart
  with_reducible
    simpa only [normalizedContourShiftCLM_apply] using EulerNonuniqueness.General.spectralTubularChart_equivariant
      diskRelabelNeutralCLM (normalizedContourShiftCLM offset) diskChartedSpectralCoordinates
      (fun value => by simpa only [normalizedContourShiftCLM_apply] using
        diskRelabelNeutralCLM_normalized_shift offset value)
      (fun value => by simpa only [normalizedContourShiftCLM_apply] using
        diskChartedSpectralCoordinates_normalized_shift offset value) increment

theorem diskSpectralTubularPartialHomeomorph_apply (increment : PeriodicC1HolderHalf) :
    diskSpectralTubularPartialHomeomorph increment = diskSpectralTubularChart increment := by
  simp only [diskSpectralTubularPartialHomeomorph, HasStrictFDerivAt.toPartialHomeomorph_coe]

theorem diskSpectralTubularChart_inverse_exists_continuousVector_radius :
    ∃ radius > 0, ∀ data : PeriodicC1HolderHalf, ‖data‖ < radius →
      data ∈ contourContinuousVectorSubmodule →
      diskSpectralTubularPartialHomeomorph.symm data ∈ contourContinuousVectorSubmodule := by
  have atZero : diskSpectralTubularPartialHomeomorph 0 = 0 := by
    rw [diskSpectralTubularPartialHomeomorph_apply, diskSpectralTubularChart_zero]
  have equivariant (offset : ℝ) (increment : PeriodicC1HolderHalf) :
      diskSpectralTubularPartialHomeomorph (normalizedContourShiftCLM offset increment) =
        normalizedContourShiftCLM offset (diskSpectralTubularPartialHomeomorph increment) := by
    simp only [diskSpectralTubularPartialHomeomorph_apply, normalizedContourShiftCLM_apply,
      diskSpectralTubularChart_normalized_shift]
  have zeroFixed (offset : ℝ) : normalizedContourShiftCLM offset (0 : PeriodicC1HolderHalf) = 0 := by
    exact (normalizedContourShiftCLM offset).map_zero
  unfold contourContinuousVectorSubmodule
  with_reducible
    simpa only [sub_zero] using EulerNonuniqueness.General.PartialHomeomorph.exists_inverse_continuousVector_radius
      diskSpectralTubularPartialHomeomorph normalizedContourShiftCLM (0 : PeriodicC1HolderHalf)
      diskSpectralTubularPartialHomeomorph_zero_mem_source atZero
      (fun offset value => by simpa only [normalizedContourShiftCLM_apply] using normalizedContourShift_norm offset value)
      zeroFixed equivariant

end EulerNonuniqueness.Paper
