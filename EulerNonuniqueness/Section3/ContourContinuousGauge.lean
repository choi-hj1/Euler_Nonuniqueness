import EulerNonuniqueness.Section3.ContourContinuousVectors
import EulerNonuniqueness.Section3.ContourCentroidGauge
import EulerNonuniqueness.Section3.DiskChartedEulerField

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance continuousGaugeC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph
local instance continuousGaugeHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance continuousGaugeC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourContinuousVectorSubmodule_constant (value : ℂ) :
    c1Constant value ∈ contourContinuousVectorSubmodule := by
  have circleContinuous : Continuous standardCircle := standardCircleBanach.val.1.continuous
  have inverseContinuous : Continuous (fun offset => (standardCircle offset)⁻¹) :=
    circleContinuous.inv₀ (fun offset => by
      exact norm_ne_zero_iff.mp (by rw [standardCircle_norm]; norm_num))
  have scalarContinuous : Continuous (fun offset : ℝ => (standardCircle offset)⁻¹ * value) :=
    inverseContinuous.mul continuous_const
  have actual := c1ConstantCLM.continuous.comp scalarContinuous
  change Continuous (fun offset => normalizedContourShiftCLM offset (c1Constant value))
  convert actual using 1
  funext offset
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem contourContinuousVectorSubmodule_constant_product (value : ℂ) (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule) :
    c1Product (c1Constant value) data ∈ contourContinuousVectorSubmodule := by
  have orbit : Continuous (fun offset => normalizedContourShiftCLM offset data) := member
  have actual := (c1ProductCLM (c1Constant value)).continuous.comp orbit
  change Continuous (fun offset => normalizedContourShiftCLM offset (c1Product (c1Constant value) data))
  convert actual using 1
  funext offset
  apply PeriodicC1HolderHalf.ext_value
  intro label
  change (standardCircle offset)⁻¹ * (value * data.val.1 (label + offset)) =
    value * ((standardCircle offset)⁻¹ * data.val.1 (label + offset))
  ring

theorem contourContinuousVectorSubmodule_rotating_self (data : PeriodicC1HolderHalf)
    (member : data ∈ contourContinuousVectorSubmodule)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    diskEulerRotatingField data ∈ contourContinuousVectorSubmodule := by
  have first : Continuous (fun offset => normalizedContourShiftCLM offset (extendedContourVelocity data)) :=
    contourContinuousVectorSubmodule_velocity data member small
  have second : Continuous (fun offset => normalizedContourShiftCLM offset
      (c1Product (c1Constant (Complex.I / 2)) data)) :=
    contourContinuousVectorSubmodule_constant_product _ data member
  change Continuous (fun offset => normalizedContourShiftCLM offset (diskEulerRotatingField data))
  simpa only [diskEulerRotatingField, map_sub] using first.sub second

theorem contourContinuousVectorSubmodule_centroid_projection (data direction : PeriodicC1HolderHalf)
    (member : direction ∈ contourContinuousVectorSubmodule) :
    contourCentroidGaugeProjection data direction ∈ contourContinuousVectorSubmodule := by
  have first : Continuous (fun offset => normalizedContourShiftCLM offset direction) := member
  have second : Continuous (fun offset => normalizedContourShiftCLM offset
      (c1Constant ((fderiv ℝ contourCentroidFunctional data) direction))) :=
    contourContinuousVectorSubmodule_constant _
  change Continuous (fun offset => normalizedContourShiftCLM offset
    (direction - c1Constant ((fderiv ℝ contourCentroidFunctional data) direction)))
  simpa only [map_sub] using first.sub second

end EulerNonuniqueness.Paper
