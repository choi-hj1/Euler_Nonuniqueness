import EulerNonuniqueness.Section3.DiskSpectralFiberRegularity
import EulerNonuniqueness.Section3.DiskSpectralTubularChart
import EulerNonuniqueness.General.SpectralSecondRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete
  chartedThirdBilinearGroup chartedThirdBilinearSpace chartedThirdBilinearComplete

local instance spectralSecondRegularityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskChartedNeutralOperator_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskChartedNeutralOperator
      (0 : PeriodicC1HolderHalf) := by
  have projectionRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_continuousLinearMap
    (Domain := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf) diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)
  have fieldRegular : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear (fderiv ℝ diskChartedEulerField)
      (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
    rw [map_zero]
    with_reducible_and_instances
      exact diskChartedEulerField_derivative_hasLipschitzSecondDerivativeNear
  unfold diskChartedNeutralOperator
  with_reducible_and_instances
    exact EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.comp
      (outer := fderiv ℝ diskChartedEulerField)
      (inner := fun parameter : PeriodicC1HolderHalf => diskRelabelNeutralCLM parameter)
      fieldRegular projectionRegular

theorem diskChartedSpectralCoordinates_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskChartedSpectralCoordinates
      (0 : PeriodicC1HolderHalf) := by
  unfold diskChartedSpectralCoordinates
  with_reducible_and_instances
    exact EulerNonuniqueness.General.cubicSpectralIntertwiner_comp_hasLipschitzSecondDerivativeNear
      (Space := PeriodicC1HolderHalf) (Parameter := PeriodicC1HolderHalf)
      diskChartedNeutralOperator diskRotatingDerivative 0 diskChartedNeutralOperator_hasLipschitzSecondDerivativeNear

theorem diskSpectralTubularChart_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskSpectralTubularChart
      (0 : PeriodicC1HolderHalf) := by
  unfold diskSpectralTubularChart
  with_reducible_and_instances
    exact EulerNonuniqueness.General.spectralTubularChart_hasLipschitzSecondDerivativeNear
      (Space := PeriodicC1HolderHalf) diskRelabelNeutralCLM diskChartedSpectralCoordinates
      diskChartedSpectralCoordinates_hasLipschitzSecondDerivativeNear

end EulerNonuniqueness.Paper
