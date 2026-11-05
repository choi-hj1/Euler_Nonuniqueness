import EulerNonuniqueness.Section3.DiskNeutralContinuousVectors
import EulerNonuniqueness.Section3.DiskChartedSpectralTrivialization
import EulerNonuniqueness.General.LinearEquivariantInverseDerivative

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance chartedShiftC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

def normalizedContourShiftCLE (offset : ℝ) : PeriodicC1HolderHalf ≃L[ℝ] PeriodicC1HolderHalf :=
  ContinuousLinearEquiv.equivOfInverse (normalizedContourShiftCLM offset) (normalizedContourShiftCLM (-offset))
    (fun data => normalizedContourShift_inverse offset data)
    (fun data => by simpa only [neg_neg] using normalizedContourShift_inverse (-offset) data)

theorem normalizedContourShiftCLE_apply (offset : ℝ) (data : PeriodicC1HolderHalf) :
    normalizedContourShiftCLE offset data = normalizedContourShift offset data := rfl

theorem normalizedContourShiftCLE_toCLM (offset : ℝ) :
    (normalizedContourShiftCLE offset).toContinuousLinearMap = normalizedContourShiftCLM offset := rfl

theorem extendedContourVelocity_normalized_shift_global (data : PeriodicC1HolderHalf) (offset : ℝ) :
    extendedContourVelocity (normalizedContourShift offset data) = normalizedContourShift offset (extendedContourVelocity data) := by
  by_cases small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))
  · exact extendedContourVelocity_normalized_shift data offset small
  · have shiftedNot : ¬‖normalizedContourShift offset data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
      rw [normalizedContourShift_distance_circle]
      exact small
    simp only [extendedContourVelocity, dif_neg shiftedNot, dif_neg small]
    exact (map_zero (normalizedContourShiftCLM offset)).symm

theorem normalizedContourShift_constant_product (offset : ℝ) (scalar : ℂ) (data : PeriodicC1HolderHalf) :
    normalizedContourShift offset (c1Product (c1Constant scalar) data) =
      c1Product (c1Constant scalar) (normalizedContourShift offset data) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (standardCircle offset)⁻¹ * (scalar * data.val.1 (label + offset)) =
    scalar * ((standardCircle offset)⁻¹ * data.val.1 (label + offset))
  ring

theorem diskEulerRotatingField_normalized_shift (offset : ℝ) (data : PeriodicC1HolderHalf) :
    diskEulerRotatingField (normalizedContourShift offset data) = normalizedContourShift offset (diskEulerRotatingField data) := by
  unfold diskEulerRotatingField
  rw [extendedContourVelocity_normalized_shift_global]
  change normalizedContourShift offset (extendedContourVelocity data) -
      c1Product (c1Constant (Complex.I / 2)) (normalizedContourShift offset data) =
    normalizedContourShiftCLM offset (extendedContourVelocity data - c1Product (c1Constant (Complex.I / 2)) data)
  rw [map_sub, normalizedContourShiftCLM_apply, normalizedContourShiftCLM_apply,
    normalizedContourShift_constant_product]

theorem diskStationaryChart_derivative_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    (fderiv ℝ diskStationaryChart (normalizedContourShift offset increment)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (fderiv ℝ diskStationaryChart increment) := by
  have actual := EulerNonuniqueness.General.fderiv_linear_equivariant_global diskStationaryChart
    (normalizedContourShiftCLE offset) (fun value => diskStationaryChart_normalized_shift offset value) increment
  simpa only [normalizedContourShiftCLE_toCLM, normalizedContourShiftCLE_apply] using actual

theorem diskChartInverseDerivative_normalized_shift (offset : ℝ) (increment direction : PeriodicC1HolderHalf) :
    diskChartInverseDerivative (normalizedContourShift offset increment) (normalizedContourShift offset direction) =
      normalizedContourShift offset (diskChartInverseDerivative increment direction) := by
  have actual := EulerNonuniqueness.General.ring_inverse_intertwining (normalizedContourShiftCLE offset)
    (fderiv ℝ diskStationaryChart (normalizedContourShift offset increment)) (fderiv ℝ diskStationaryChart increment)
    (by simpa only [normalizedContourShiftCLE_toCLM] using diskStationaryChart_derivative_normalized_shift offset increment) direction
  simpa only [diskChartInverseDerivative, normalizedContourShiftCLE_apply] using actual

theorem diskChartedEulerField_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    diskChartedEulerField (normalizedContourShift offset increment) = normalizedContourShift offset (diskChartedEulerField increment) := by
  unfold diskChartedEulerField
  rw [diskStationaryChart_normalized_shift, diskEulerRotatingField_normalized_shift,
    diskChartInverseDerivative_normalized_shift]

theorem diskChartedEulerField_derivative_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    (fderiv ℝ diskChartedEulerField (normalizedContourShift offset increment)).comp (normalizedContourShiftCLM offset) =
      (normalizedContourShiftCLM offset).comp (fderiv ℝ diskChartedEulerField increment) := by
  have actual := EulerNonuniqueness.General.fderiv_linear_equivariant_global diskChartedEulerField
    (normalizedContourShiftCLE offset) (fun value => diskChartedEulerField_normalized_shift offset value) increment
  simpa only [normalizedContourShiftCLE_toCLM, normalizedContourShiftCLE_apply] using actual

end EulerNonuniqueness.Paper
