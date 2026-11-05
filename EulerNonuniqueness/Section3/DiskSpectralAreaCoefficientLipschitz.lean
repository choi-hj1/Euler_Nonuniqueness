import EulerNonuniqueness.Section3.DiskSpectralAreaCoefficient

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd chartedBilinearGroup chartedBilinearModule
  stationaryAreaRemainderOperatorGroup stationaryAreaRemainderOperatorSpace

theorem diskSpectralAreaRadialCoefficient_neutral_parameter (parameter : PeriodicC1HolderHalf) :
    diskSpectralAreaRadialCoefficient (diskRelabelNeutralCLM parameter) =
      diskSpectralAreaRadialCoefficient parameter := by
  unfold diskSpectralAreaRadialCoefficient
  rw [diskRelabelNeutralCLM_idempotent]

theorem diskSpectralAreaRadialCoefficient_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear diskSpectralAreaRadialCoefficient (0 : PeriodicC1HolderHalf) := by
  have derivativeRegular := diskSpectralTubularArea_hasLipschitzDerivativeNear.2
  have atNeutral : EulerNonuniqueness.General.LipschitzNear
      (fderiv ℝ diskSpectralTubularArea) (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)) := by
    simpa only [map_zero] using derivativeRegular
  have projectionRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    (Space := PeriodicC1HolderHalf) (Target := PeriodicC1HolderHalf) diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)
  let evaluate : (PeriodicC1HolderHalf →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ standardCircleBanach
  have evaluationRegular := EulerNonuniqueness.General.hasLipschitzDerivativeNear_continuousLinearMap
    (Space := PeriodicC1HolderHalf →L[ℝ] ℝ) (Target := ℝ) evaluate
    (fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM (0 : PeriodicC1HolderHalf)))
  unfold diskSpectralAreaRadialCoefficient
  exact EulerNonuniqueness.General.LipschitzNear.comp (outer := evaluate)
    (inner := fun state : PeriodicC1HolderHalf =>
      fderiv ℝ diskSpectralTubularArea (diskRelabelNeutralCLM state)) (point := 0)
    evaluationRegular.lipschitzNear (atNeutral.comp projectionRegular.lipschitzNear)

end

end EulerNonuniqueness.Paper
