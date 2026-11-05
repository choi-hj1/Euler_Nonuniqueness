import EulerNonuniqueness.Section3.ContourCauchySecondOperatorLipschitz

open Set Metric

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondOperatorLipHolderModule secondOperatorLipC1Module
  derivativeOperatorHolderSpace derivativeOperatorC1Space
  derivativeOperatorGroup derivativeOperatorModule derivativeOperatorSpace
  derivativeDensityOperatorGroup derivativeDensityOperatorModule derivativeDensityOperatorSpace
  secondFamilyDensityUniformAdd secondFamilyDensityTopologicalAdd
  secondFamilyDerivativeGroup secondFamilyDerivativeSub

local instance secondLineDerivativeAddCommGroup : AddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  secondFamilyDerivativeGroup.toAddCommGroup

local instance secondLineDensityContinuousAdd : ContinuousAdd
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  (inferInstance : IsTopologicalAddGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)).toContinuousAdd

local instance secondLineDerivativeModule : Module ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance secondLineDerivativeSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

def extendedContourCauchySecondOperatorCLM (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  fderiv ℂ extendedContourCauchyDerivativeDensityCLM data

theorem extendedContourCauchySecondOperatorCLM_apply
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchySecondOperatorCLM data first density second =
      contourCauchySecondVariation data first second density := by
  unfold extendedContourCauchySecondOperatorCLM
  rw [HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (hasFDerivAt_extendedContourCauchyDerivativeDensityCLM data near gap small),
    secondVariationDensity_flip_apply, contourCauchySecondVariationCLM_apply]

theorem extendedContourCauchySecondOperatorCLM_continuousOn_complex_line
    (data direction : PeriodicC1HolderHalf) {domain : Set ℂ}
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ∀ point ∈ domain,
      ‖data + point • direction - standardCircleBanach‖ < innerRadius) :
    ContinuousOn (fun point : ℂ => extendedContourCauchySecondOperatorCLM
      (data + point • direction)) domain := by
  let constant := (16 * contourCauchyParameterOperatorConstant outerRadius /
    (outerRadius - innerRadius) ^ 2) * ‖direction‖
  have constantNonnegative : 0 ≤ constant := by
    have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg
      (nonnegative.trans gap.le) small
    positivity
  apply (LipschitzOnWith.of_dist_le_mul (K := ⟨constant, constantNonnegative⟩) ?_).continuousOn
  intro first firstInside second secondInside
  rw [dist_eq_norm, dist_eq_norm first second]
  have bound := fderiv_extendedContourCauchyDerivativeDensityCLM_difference_bound
    (data + first • direction) (data + second • direction) nonnegative gap small
    (nearby first firstInside) (nearby second secondInside)
  have difference : data + first • direction - (data + second • direction) =
      (first - second) • direction := by
    have scalarDifference : (first - second) • direction = first • direction - second • direction := by
      with_reducible exact sub_smul first second direction
    rw [scalarDifference]
    abel
  have scaledNorm : ‖(first - second) • direction‖ = ‖first - second‖ * ‖direction‖ := by
    with_reducible exact norm_smul (first - second) direction
  rw [difference, scaledNorm] at bound
  exact bound.trans_eq (by
    change _ = constant * ‖first - second‖
    dsimp only [constant]
    ring)

end

end EulerNonuniqueness.Paper
