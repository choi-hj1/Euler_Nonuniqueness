import EulerNonuniqueness.Section3.ContourCauchyJointThirdRegularity
import EulerNonuniqueness.Section3.ContourVelocityValueHigherDerivative
import EulerNonuniqueness.Section3.HolderDifferentialAlgebra
import EulerNonuniqueness.Section3.C1HolderOperations

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] valueHigherHolderSpace valueHigherC1Space
  valueHigherHolderComplexModule valueHigherOperatorGroup valueHigherOperatorRealSpace
  valueHigherOperatorComplexModule valueHigherOperatorComplexSpace
  jointHigherPairOperatorGroup jointHigherPairOperatorSpace

theorem extendedContourVelocityHolderDerivativeCLM_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourVelocityHolderDerivativeCLM standardCircleBanach := by
  let density := contourHolderConjugateRealCLM.comp c1ValueHolderRealCLM
  have densityRegular := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_continuousLinearMap
    density standardCircleBanach
  have joint := extendedContourCauchyJointDerivativeCLM_hasLipschitzSecondDerivativeNear_comp_density
    (fun data => density data) densityRegular
  let paired := (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf).prod density
  let precomposition := (ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    (PeriodicC1HolderHalf × PeriodicHolderHalf) PeriodicHolderHalf).flip paired
  have inner := joint.map precomposition
  let postcomposition := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf contourHolderConjugateRealCLM
  have conjugate := inner.map postcomposition
  let scalarHolder : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
    holderProductRealCLM (c1ValueHolder (c1Constant (1 / (4 * Real.pi) : ℂ)))
  let scalarOperator := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf scalarHolder
  have scaled := conjugate.map scalarOperator
  have constant := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_const
    ((Complex.I / 4) • c1ValueHolderRealCLM) standardCircleBanach
  have expression := constant.sub scaled
  apply expression.congr
  filter_upwards [] with data
  apply ContinuousLinearMap.ext
  intro direction
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

end

end EulerNonuniqueness.Paper
