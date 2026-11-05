import EulerNonuniqueness.Section3.DiskSpectralMovingQuadraticLipschitz
import EulerNonuniqueness.Section3.DiskSpectralInverseDerivativeLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralFiberDifferential_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear
      (fun parameter : PeriodicC1HolderHalf =>
        fderiv ℝ diskChartedSpectralCoordinates (diskRelabelNeutralCLM parameter)) 0 := by
  have projectionRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf)
    diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)
  have derivativeRegular := diskChartedSpectralCoordinates_hasLipschitzDerivativeNear.2
  have atNeutral : EulerNonuniqueness.General.LipschitzNear
      (fderiv ℝ diskChartedSpectralCoordinates) (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
    simpa only [map_zero] using derivativeRegular
  exact atNeutral.comp projectionRegular.lipschitzNear

end

end EulerNonuniqueness.Paper
