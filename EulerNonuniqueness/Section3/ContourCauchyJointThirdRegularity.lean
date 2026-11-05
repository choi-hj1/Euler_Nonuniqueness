import EulerNonuniqueness.Section3.ContourRealCauchyOperatorRegularity
import EulerNonuniqueness.Section3.ContourCauchyJointHigherDerivative

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] jointHigherHolderSpace jointHigherC1Space
  jointHigherDerivativeGroup jointHigherDerivativeSpace jointHigherValueGroup jointHigherValueSpace
  jointHigherDensityGroup jointHigherDensitySpace jointHigherPairOperatorGroup jointHigherPairOperatorSpace

theorem extendedContourCauchyJointDerivativeCLM_hasLipschitzSecondDerivativeNear_comp_density
    (density : PeriodicC1HolderHalf → PeriodicHolderHalf)
    (densityRegular : EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear density standardCircleBanach) :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      (fun data => extendedContourCauchyJointDerivativeCLM data (density data)) standardCircleBanach := by
  let firstComposition := (ContinuousLinearMap.compL ℝ
    (PeriodicC1HolderHalf × PeriodicHolderHalf) PeriodicC1HolderHalf PeriodicHolderHalf).flip
      (ContinuousLinearMap.fst ℝ PeriodicC1HolderHalf PeriodicHolderHalf)
  let secondComposition := (ContinuousLinearMap.compL ℝ
    (PeriodicC1HolderHalf × PeriodicHolderHalf) PeriodicHolderHalf PeriodicHolderHalf).flip
      (ContinuousLinearMap.snd ℝ PeriodicC1HolderHalf PeriodicHolderHalf)
  have applied := EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.id ℝ (PeriodicHolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf))
    realContourCauchyDerivativeDensity_hasLipschitzSecondDerivativeNear densityRegular
  have firstRegular := applied.map firstComposition
  have secondRegular := realContourCauchyOperator_hasLipschitzSecondDerivativeNear.map secondComposition
  have expression := firstRegular.add secondRegular
  apply expression.congr
  filter_upwards [] with data
  rfl

end

end EulerNonuniqueness.Paper
