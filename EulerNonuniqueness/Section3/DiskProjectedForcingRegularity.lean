import EulerNonuniqueness.Section3.DiskPhysicalSpectralInverseRegularity
import EulerNonuniqueness.Section3.ContourGaugeOperatorTaylor

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
  centroidGaugeRegularityDerivativeGroup centroidGaugeRegularityDerivativeSpace
  centroidGaugeRegularityConstantGroup gaugeOperatorTaylorConstantSpace

local instance projectedForcingRegularityC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem contourCentroidGaugeProjection_hasLipschitzDerivativeNear_circle :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear contourCentroidGaugeProjection standardCircleBanach := by
  have smooth := contourCentroidGaugeProjection_contDiffAt_two
  exact EulerNonuniqueness.General.hasLipschitzDerivativeNear_of_contDiffAt_two smooth

theorem diskPhysicalSpectralProjectedInverse_hasLipschitzDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun point => (diskPhysicalSpectralInverseDerivative (diskPhysicalSpectralChart point)).comp
        (contourCentroidGaugeProjection (diskPhysicalSpectralChart point)))
      (0 : PeriodicC1HolderHalf) := by
  have chartRegular := diskPhysicalSpectralChart_hasLipschitzSecondDerivativeNear
  unfold EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear at chartRegular
  have projectionAt : EulerNonuniqueness.General.HasLipschitzDerivativeNear contourCentroidGaugeProjection
      (diskPhysicalSpectralChart (0 : PeriodicC1HolderHalf)) := by
    rw [diskPhysicalSpectralChart_zero]
    exact contourCentroidGaugeProjection_hasLipschitzDerivativeNear_circle
  have projectionRegular : EulerNonuniqueness.General.HasLipschitzDerivativeNear
      (fun point => contourCentroidGaugeProjection (diskPhysicalSpectralChart point)) (0 : PeriodicC1HolderHalf) :=
    EulerNonuniqueness.General.HasLipschitzDerivativeNear.comp
      (outer := contourCentroidGaugeProjection) (inner := diskPhysicalSpectralChart) projectionAt chartRegular.1
  have inverseRegular := diskPhysicalSpectralInverseDerivative_chart_hasLipschitzDerivativeNear
  exact EulerNonuniqueness.General.HasLipschitzDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf PeriodicC1HolderHalf PeriodicC1HolderHalf)
    inverseRegular projectionRegular

end EulerNonuniqueness.Paper
