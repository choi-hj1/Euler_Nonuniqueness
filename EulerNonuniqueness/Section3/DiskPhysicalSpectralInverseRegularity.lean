import EulerNonuniqueness.Section3.DiskSpectralSecondRegularity
import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseLipschitz

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

local instance physicalSpectralInverseRegularityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskSpectralTubularInverseDerivative_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear diskSpectralTubularInverseDerivative
      (0 : PeriodicC1HolderHalf) := by
  have regular := diskSpectralTubularChart_hasLipschitzSecondDerivativeNear
  unfold EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear at regular
  have jacobianRegular := regular.2
  have identity : fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible_and_instances
      exact diskSpectralTubularChart_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
  unfold diskSpectralTubularInverseDerivative
  exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_inverse_family_of_identity
    (Space := PeriodicC1HolderHalf) (fderiv ℝ diskSpectralTubularChart) jacobianRegular identity

theorem diskPhysicalSpectralChart_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskPhysicalSpectralChart
      (0 : PeriodicC1HolderHalf) := by
  have outer : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear diskStationaryChart
      (diskSpectralTubularChart (0 : PeriodicC1HolderHalf)) := by
    rw [diskSpectralTubularChart_zero]
    with_reducible_and_instances
      exact EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
        (diskStationaryChart_analyticAt (0 : PeriodicC1HolderHalf))
  unfold diskPhysicalSpectralChart
  with_reducible_and_instances
    exact EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.comp
      (outer := diskStationaryChart) (inner := diskSpectralTubularChart)
      outer diskSpectralTubularChart_hasLipschitzSecondDerivativeNear

theorem diskPhysicalSpectralInverseDerivative_chart_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun point => diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point))
      (0 : PeriodicC1HolderHalf) := by
  have regular := diskPhysicalSpectralChart_hasLipschitzSecondDerivativeNear
  unfold EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear at regular
  have jacobianRegular := regular.2
  have identity : fderiv ℝ diskPhysicalSpectralChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible_and_instances
      exact diskPhysicalSpectralChart_hasStrictFDerivAt_zero.hasFDerivAt.fderiv
  have inverseRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_inverse_family_of_identity
    (Space := PeriodicC1HolderHalf) (fderiv ℝ diskPhysicalSpectralChart) jacobianRegular identity
  exact inverseRegular.congr diskPhysicalSpectralChart_eventually_inverse_jacobian

end EulerNonuniqueness.Paper
