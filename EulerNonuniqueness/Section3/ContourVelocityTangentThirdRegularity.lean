import EulerNonuniqueness.Section3.ContourTangentInnerThirdRegularity
import EulerNonuniqueness.Section3.ContourVelocityTangentHigherDerivative

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] tangentHigherHolderSpace tangentHigherC1Space
  tangentHigherHolderComplexModule tangentHigherValueOperatorGroup tangentHigherValueOperatorSpace
  tangentHigherOperatorGroup tangentHigherOperatorRealSpace
  tangentHigherOperatorComplexModule tangentHigherOperatorComplexSpace

theorem extendedContourVelocityTangentDerivativeCLM_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourVelocityTangentDerivativeCLM standardCircleBanach := by
  let tangent := contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM
  have tangentRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_continuousLinearMap
    tangent standardCircleBanach
  have left := tangentRegular.map holderProductRealCLM
  let postcomposition := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf contourHolderConjugateRealCLM
  have inner := extendedContourTangentInnerDerivativeCLM_hasLipschitzSecondDerivativeNear.map
    postcomposition
  have first := EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf PeriodicHolderHalf PeriodicHolderHalf) left inner
  have conjugate := contourTangentInner_hasLipschitzSecondDerivativeNear.map contourHolderConjugateRealCLM
  have right := conjugate.map holderProductRealCLM.flip
  let precomposition := (ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf).flip tangent
  have second := right.map precomposition
  have sum := first.add second
  let scalarHolder : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
    holderProductRealCLM (c1ValueHolder (c1Constant (-(1 / (4 * Real.pi) : ℂ))))
  let scalarOperator := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf scalarHolder
  have expression := sum.map scalarOperator
  apply expression.congr
  filter_upwards [] with data
  apply ContinuousLinearMap.ext
  intro direction
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

end

end EulerNonuniqueness.Paper
