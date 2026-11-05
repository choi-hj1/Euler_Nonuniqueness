import EulerNonuniqueness.Section3.ContourRealCauchyDerivativeRegularity
import EulerNonuniqueness.General.LocalOperatorRegularity

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] realCauchyFamilyHolderReal realCauchyFamilyC1Real
  realCauchyFamilyHolderComplex realCauchyFamilyC1Complex
  realCauchyFamilyRealValueGroup realCauchyFamilyRealValueSpace
  realCauchyFamilyRealDerivativeGroup realCauchyFamilyRealDerivativeModule realCauchyFamilyRealDerivativeSpace
  thirdRealDensityOperatorGroup thirdRealDensityOperatorAddCommMonoid
  thirdRealDensityOperatorSpace thirdRealDensityOperatorModule
  thirdDensitySourceComplexModule thirdDensitySourceComplexSMul
  thirdDensitySourceBoundedSMul thirdDensitySourceContinuousSMul

local instance thirdRealValueDerivativeGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance thirdRealValueDerivativeSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

theorem fderiv_realContourCauchyOperatorCLM_eq_flip
    (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    fderiv ℝ realContourCauchyOperatorCLM data =
      (ContinuousLinearMap.flipₗᵢ ℝ PeriodicHolderHalf PeriodicC1HolderHalf PeriodicHolderHalf)
        (realContourCauchyDerivativeDensityCLM data) := by
  have regular := differentiableAt_realContourCauchyOperatorCLM data near small
  apply ContinuousLinearMap.ext
  intro direction
  apply ContinuousLinearMap.ext
  intro density
  let evaluation := ContinuousLinearMap.apply ℝ PeriodicHolderHalf density
  have outerDerivative := evaluation.hasFDerivAt (x := realContourCauchyOperatorCLM data)
  have innerDerivative := DifferentiableAt.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℝ] PeriodicHolderHalf) regular
  have evaluatedDerivative := outerDerivative.comp data innerDerivative
  have originalDerivative := hasFDerivAt_extendedContourCauchy data density near small
  have direct := HasFDerivAt.restrictScalars ℝ (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) originalDerivative
  have functionEquality : (fun current => evaluation (realContourCauchyOperatorCLM current)) =
      (fun current => extendedContourCauchy current density) := by
    funext current
    exact realContourCauchyOperatorCLM_apply current density
  change HasFDerivAt (fun current => evaluation (realContourCauchyOperatorCLM current))
    (evaluation.comp (fderiv ℝ realContourCauchyOperatorCLM data)) data at evaluatedDerivative
  rw [functionEquality] at evaluatedDerivative
  have derivativeEquality := evaluatedDerivative.unique direct
  have evaluated := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf =>
    operator direction) derivativeEquality
  have actual : (contourCauchyDerivativeCLM data density near small) direction =
      contourCauchyDirectionalDerivative data direction density := rfl
  change (fderiv ℝ realContourCauchyOperatorCLM data direction) density =
    realContourCauchyDerivativeDensityCLM data density direction
  rw [realContourCauchyDerivativeDensityCLM_apply data direction density near small]
  change (fderiv ℝ realContourCauchyOperatorCLM data direction) density =
    (contourCauchyDerivativeCLM data density near small) direction at evaluated
  exact evaluated.trans actual

theorem realContourCauchyOperator_hasLipschitzSecondDerivativeNear :
    EulerNonuniqueness.General.HasLipschitzSecondDerivativeNear
      realContourCauchyOperatorCLM standardCircleBanach := by
  let flip := (ContinuousLinearMap.flipₗᵢ ℝ PeriodicHolderHalf PeriodicC1HolderHalf PeriodicHolderHalf).toContinuousLinearEquiv.toContinuousLinearMap
  have densityRegular := realContourCauchyDerivativeDensity_hasLipschitzSecondDerivativeNear.1
  have expression := EulerNonuniqueness.General.hasLipschitzDerivativeNear_flip
    (Domain := PeriodicC1HolderHalf) (First := PeriodicHolderHalf)
    (Second := PeriodicC1HolderHalf) (Target := PeriodicHolderHalf) densityRegular
  let radius := min 1 (2 / (3 * Real.pi)) / 2
  have positive : 0 < radius := by dsimp only [radius]; positivity
  have thresholdPositive : 0 < min 1 (2 / (3 * Real.pi)) := by positivity
  have small : radius < min 1 (2 / (3 * Real.pi)) := by
    dsimp only [radius]
    linarith
  have nearby : ∀ᶠ data in 𝓝 standardCircleBanach, ‖data - standardCircleBanach‖ < radius := by
    filter_upwards [ball_mem_nhds standardCircleBanach positive] with data inside
    with_reducible_and_instances simpa only [mem_ball, dist_eq_norm data standardCircleBanach] using inside
  have derivativeEquality : fderiv ℝ realContourCauchyOperatorCLM =ᶠ[𝓝 standardCircleBanach]
      (fun data => flip (realContourCauchyDerivativeDensityCLM data)) := by
    filter_upwards [nearby] with data near
    exact fderiv_realContourCauchyOperatorCLM_eq_flip data near small
  have derivativeRegular := expression.congr derivativeEquality
  refine ⟨⟨?_, derivativeRegular.lipschitzNear⟩, derivativeRegular⟩
  filter_upwards [nearby] with data near
  exact differentiableAt_realContourCauchyOperatorCLM data near small

end

end EulerNonuniqueness.Paper
