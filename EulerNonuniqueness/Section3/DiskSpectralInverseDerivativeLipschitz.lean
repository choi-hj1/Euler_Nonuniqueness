import EulerNonuniqueness.Section3.DiskSpectralTubularEquation
import EulerNonuniqueness.General.InverseOperatorLocalLipschitz

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] chartedBilinearC1Space chartedBilinearC1ContinuousAdd
  chartedBilinearOperatorGroup chartedBilinearOperatorModule chartedBilinearOperatorSpace
  chartedBilinearOperatorUniformAdd chartedBilinearOperatorContinuousAdd
  chartedBilinearGroup chartedBilinearModule
  diskChartedEulerOperatorRing diskChartedEulerOperatorAlgebra diskChartedEulerOperatorComplete

theorem diskSpectralTubularInverseDerivative_lipschitzNear :
    EulerNonuniqueness.General.LipschitzNear diskSpectralTubularInverseDerivative
      (0 : PeriodicC1HolderHalf) := by
  have identity : fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf) =
      ContinuousLinearMap.id ℝ PeriodicC1HolderHalf := by
    with_reducible
      exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
        (HasStrictFDerivAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
          diskSpectralTubularChart_hasStrictFDerivAt_zero)
  have inverseRegular := EulerNonuniqueness.General.inverse_operator_lipschitzNear_identity
    (Space := PeriodicC1HolderHalf)
  have jacobianRegular := diskSpectralTubularChart_hasLipschitzDerivativeNear.2
  have inverseAt : EulerNonuniqueness.General.LipschitzNear
      (Ring.inverse : (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf) →
        PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf)
      (fderiv ℝ diskSpectralTubularChart (0 : PeriodicC1HolderHalf)) := by
    rw [identity]
    exact inverseRegular
  unfold diskSpectralTubularInverseDerivative
  with_reducible_and_instances
    exact inverseAt.comp jacobianRegular

end

end EulerNonuniqueness.Paper
