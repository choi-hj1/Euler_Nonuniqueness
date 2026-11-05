import EulerNonuniqueness.Section3.ContourCauchyJointThirdRegularity
import EulerNonuniqueness.Section3.ContourTangentInnerHigherDerivative
import EulerNonuniqueness.General.LocalDerivativeFieldRegularity
import EulerNonuniqueness.Section3.C1HolderOperations

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] innerHigherHolderSpace innerHigherC1Space
  innerHigherEndGroup innerHigherEndSpace innerHigherHolderComplexModule
  innerHigherOperatorGroup innerHigherOperatorRealSpace
  innerHigherOperatorComplexModule innerHigherOperatorComplexSpace
  jointHigherPairOperatorGroup jointHigherPairOperatorSpace

local instance thirdInnerOperatorComplete : CompleteSpace
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.instCompleteSpace (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
local instance thirdInnerPairMapGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance thirdInnerPairMapSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf × PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf × PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem extendedContourTangentInnerDerivativeCLM_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      extendedContourTangentInnerDerivativeCLM standardCircleBanach := by
  have small : ‖standardCircleBanach - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) := by
    have equal : standardCircleBanach - standardCircleBanach = (0 : PeriodicC1HolderHalf) := by
      apply PeriodicC1HolderHalf.ext_value
      intro label
      change standardCircleBanach.val.1 label - standardCircleBanach.val.1 label = 0
      exact sub_self _
    rw [equal]
    have zeroNorm : ‖(0 : PeriodicC1HolderHalf)‖ = (0 : ℝ) := by
      with_reducible_and_instances
        exact norm_zero (E := PeriodicC1HolderHalf)
    exact zeroNorm.trans_lt (by positivity)
  have quotient := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (analyticAt_extendedContourTangentQuotient standardCircleBanach small)
  have quotientDerivative := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_analyticAt
    (analyticAt_contourQuotientDerivativeCLM standardCircleBanach small)
  have joint := extendedContourCauchyJointDerivativeCLM_hasLipschitzSecondDerivativeNear_comp_density
    extendedContourTangentQuotient quotient
  have identity := EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_const
    (ContinuousLinearMap.id ℝ PeriodicC1HolderHalf) standardCircleBanach
  let product := (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf) ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have paired := (identity.prodMk quotientDerivative).map product
  have composed := EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear.bilinear
    (ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
      (PeriodicC1HolderHalf × PeriodicHolderHalf) PeriodicHolderHalf) joint paired
  let scalarHolder : PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf :=
    holderProductRealCLM (c1ValueHolder (c1Constant ((Real.pi : ℂ) * Complex.I)))
  let scalarOperator := ContinuousLinearMap.compL ℝ PeriodicC1HolderHalf
    PeriodicHolderHalf PeriodicHolderHalf scalarHolder
  have scaled := quotientDerivative.map scalarOperator
  have expression := composed.add scaled
  apply expression.congr
  filter_upwards [] with data
  apply ContinuousLinearMap.ext
  intro direction
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem contourTangentInner_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      contourTangentInner standardCircleBanach := by
  have regular := extendedContourTangentInnerDerivativeCLM_hasLipschitzSecondDerivativeNear.1
  apply EulerNonuniqueness.General.hasLipschitzSecondDerivativeNear_of_derivative_field
    (field := extendedContourTangentInnerDerivativeCLM) (point := standardCircleBanach) _ regular
  let radius := min 1 (2 / (3 * Real.pi)) / 2
  have positive : 0 < radius := by dsimp only [radius]; positivity
  have small : radius < min 1 (2 / (3 * Real.pi)) := by
    dsimp only [radius]
    have threshold : 0 < min 1 (2 / (3 * Real.pi)) := by positivity
    linarith
  filter_upwards [Metric.ball_mem_nhds standardCircleBanach positive] with data inside
  have near : ‖data - standardCircleBanach‖ < radius := by
    with_reducible_and_instances
      simpa only [Metric.mem_ball, dist_eq_norm data standardCircleBanach] using inside
  have actual := hasFDerivAt_contourTangentInner data near small
  rw [← extendedContourTangentInnerDerivativeCLM_eq data near small] at actual
  exact actual

end

end EulerNonuniqueness.Paper
