import EulerNonuniqueness.Section3.HilbertContinuousVectors
import EulerNonuniqueness.Section3.DiskStationaryChart
import EulerNonuniqueness.General.EquivariantLocalInverseContinuousVectors

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance stationaryContinuousC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem diskRelativeC1_normalized_shift (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    diskRelativeC1 (normalizedContourShift offset direction) = contourLabelShiftCCLM offset (diskRelativeC1 direction) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value]
  change star (standardCircle label) * (normalizedContourShift offset direction).val.1 label =
    star (standardCircle (label + offset)) * direction.val.1 (label + offset)
  rw [normalizedContourShift_value, standardCircle_add, star_mul]
  simp only [standardCircle_star_eq_inv]
  ring

theorem diskAngularCLM_normalized_shift (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    diskAngularCLM (normalizedContourShift offset direction) = contourLabelShiftCCLM offset (diskAngularCLM direction) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [contourLabelShiftCCLM_value, diskAngularCLM_value, diskAngularCLM_value,
    diskRelativeC1_normalized_shift, contourLabelShiftCCLM_value]

theorem diskNeutralCLM_normalized_shift (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    diskNeutralCLM (normalizedContourShift offset direction) = contourLabelShiftCCLM offset (diskNeutralCLM direction) := by
  rw [diskNeutralCLM_apply, diskNeutralCLM_apply, map_add,
    diskAngularCLM_normalized_shift, ← diskRadialPart_labelShift, periodicHilbertC1_labelShift]

theorem diskStationaryChart_normalized_shift (offset : ℝ) (increment : PeriodicC1HolderHalf) :
    diskStationaryChart (normalizedContourShift offset increment) =
      normalizedContourShift offset (diskStationaryChart increment) := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rw [normalizedContourShift_value offset (diskStationaryChart increment) label]
  simp only [diskStationaryChart_value, diskNeutralCLM_normalized_shift, contourLabelShiftCCLM_value,
    normalizedContourShift_value, standardCircle_add]
  have nonzero : standardCircle offset ≠ 0 := by simp only [standardCircle, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  field_simp
  <;> ring

theorem diskStationaryChart_mem_contourContinuousVectorSubmodule (increment : PeriodicC1HolderHalf)
    (member : increment ∈ contourContinuousVectorSubmodule) :
    diskStationaryChart increment ∈ contourContinuousVectorSubmodule := by
  have chartContinuous : Continuous diskStationaryChart :=
    continuous_iff_continuousAt.mpr (fun point => (diskStationaryChart_analyticAt point).continuousAt)
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset increment) := member
  have composition := chartContinuous.comp orbit
  change Continuous (fun offset => normalizedContourShiftCLM offset (diskStationaryChart increment))
  simpa only [Function.comp_def, normalizedContourShiftCLM_apply, diskStationaryChart_normalized_shift] using composition

theorem diskStationaryChart_inverse_exists_continuousVector_radius :
    ∃ radius > 0, ∀ data : PeriodicC1HolderHalf, ‖data - standardCircleBanach‖ < radius →
      data ∈ contourContinuousVectorSubmodule →
      diskStationaryChartPartialHomeomorph.symm data ∈ contourContinuousVectorSubmodule := by
  have atZero : diskStationaryChartPartialHomeomorph 0 = standardCircleBanach := diskStationaryChart_zero
  have equivariant (offset : ℝ) (increment : PeriodicC1HolderHalf) :
      diskStationaryChartPartialHomeomorph (normalizedContourShiftCLM offset increment) =
        normalizedContourShiftCLM offset (diskStationaryChartPartialHomeomorph increment) :=
    diskStationaryChart_normalized_shift offset increment
  unfold contourContinuousVectorSubmodule
  with_reducible
    exact EulerNonuniqueness.General.PartialHomeomorph.exists_inverse_continuousVector_radius
      diskStationaryChartPartialHomeomorph normalizedContourShiftCLM standardCircleBanach
      diskStationaryChart_zero_mem_source atZero
      (fun offset value => by simpa only [normalizedContourShiftCLM_apply] using normalizedContourShift_norm offset value)
      (fun offset => by simpa only [normalizedContourShiftCLM_apply] using normalizedContourShift_circle offset) equivariant

end EulerNonuniqueness.Paper
