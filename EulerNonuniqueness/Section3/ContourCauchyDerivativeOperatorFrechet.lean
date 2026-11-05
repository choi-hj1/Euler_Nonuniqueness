import EulerNonuniqueness.Section3.ContourCauchyOperatorFrechet
import EulerNonuniqueness.Section3.ContourCauchySecondFrechet
import EulerNonuniqueness.Section3.ContourSecondVariationDensityCLM
import EulerNonuniqueness.Section3.QuadraticFrechetCriterion

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance derivativeOperatorHolderSpace : NormedSpace ℂ PeriodicHolderHalf := Submodule.normedSpace complexPeriodicHolderGraph
local instance derivativeOperatorC1Space : NormedSpace ℂ PeriodicC1HolderHalf := Submodule.normedSpace complexPeriodicC1HolderGraph
local instance derivativeOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance derivativeOperatorModule : Module ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance derivativeOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance derivativeDensityOperatorGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance derivativeDensityOperatorModule : Module ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicHolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance derivativeDensityOperatorSpace : NormedSpace ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

def extendedContourCauchyDerivativeDensityCLM (data : PeriodicC1HolderHalf) :
    PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf := by
  classical
  exact if small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi)) then
    ContinuousLinearMap.flip (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
      (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (contourCauchyFirstVariationCLM data
      (radius := (‖data - standardCircleBanach‖ + min 1 (2 / (3 * Real.pi))) / 2)
      (by linarith) (by linarith)) else 0

def contourCauchyDerivativeDensitySecondCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  ContinuousLinearMap.flip (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (contourCauchySecondVariationDensityCLM data near gap small)

theorem extendedContourCauchyDerivativeDensityCLM_apply (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    extendedContourCauchyDerivativeDensityCLM data density =
      fderiv ℂ (fun current => extendedContourCauchy current density) data := by
  classical
  rw [extendedContourCauchyDerivativeDensityCLM, dif_pos small]
  obtain ⟨radius, near, radius_small⟩ := exists_between small
  rw [HasFDerivAt.fderiv (𝕜 := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (hasFDerivAt_extendedContourCauchy data density near radius_small)]
  apply ContinuousLinearMap.ext
  intro direction
  rfl

theorem secondVariationDensity_flip_apply (data increment : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    contourCauchyDerivativeDensitySecondCLM data near gap small increment density =
      contourCauchySecondVariationCLM data density near gap small increment := rfl

theorem contourCauchyDerivativeDensityCLM_remainder_density_bound (data increment : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖(extendedContourCauchyDerivativeDensityCLM (data + increment) - extendedContourCauchyDerivativeDensityCLM data -
      contourCauchyDerivativeDensitySecondCLM data near gap small increment) density‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 * ‖density‖ := by
  have perturbed_near : ‖data + increment - standardCircleBanach‖ < innerRadius := by
    have estimate : ‖data + increment - standardCircleBanach‖ ≤ ‖data - standardCircleBanach‖ + ‖increment‖ := by
      convert norm_add_le (data - standardCircleBanach) increment using 1 <;> congr 1 <;> abel
    linarith
  rw [ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicHolderHalf)
      (M₂ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf),
    ContinuousLinearMap.sub_apply (R := ℂ) (R₂ := ℂ) (M := PeriodicHolderHalf)
      (M₂ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf),
    extendedContourCauchyDerivativeDensityCLM_apply _ _ (perturbed_near.trans (gap.trans small)),
    extendedContourCauchyDerivativeDensityCLM_apply _ _ (near.trans (gap.trans small)),
    secondVariationDensity_flip_apply]
  exact (contourCauchy_fderiv_quadratic_remainder_bound data increment density near gap small increment_small).trans_eq (by ring)

theorem contourCauchyDerivativeDensityCLM_remainder_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (increment_small : ‖increment‖ ≤ (innerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖extendedContourCauchyDerivativeDensityCLM (data + increment) - extendedContourCauchyDerivativeDensityCLM data -
      contourCauchyDerivativeDensitySecondCLM data near gap small increment‖ ≤
      (8 * contourCauchyParameterOperatorConstant outerRadius /
        (innerRadius - ‖data - standardCircleBanach‖) ^ 2) * ‖increment‖ ^ 2 := by
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg
    ((norm_nonneg _).trans (near.trans gap).le) small
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (extendedContourCauchyDerivativeDensityCLM (data + increment) - extendedContourCauchyDerivativeDensityCLM data -
      contourCauchyDerivativeDensitySecondCLM data near gap small increment)
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) parameter_nonnegative) (sq_nonneg _)) (sq_nonneg _))
  intro density
  exact contourCauchyDerivativeDensityCLM_remainder_density_bound data increment density near gap small increment_small

theorem hasFDerivAt_extendedContourCauchyDerivativeDensityCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt extendedContourCauchyDerivativeDensityCLM
      (contourCauchyDerivativeDensitySecondCLM data near gap small) data := by
  exact EulerNonuniqueness.General.hasFDerivAt_of_quadratic_remainder
    (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (function := extendedContourCauchyDerivativeDensityCLM)
    (derivative := contourCauchyDerivativeDensitySecondCLM data near gap small) (point := data)
    (radius := (innerRadius - ‖data - standardCircleBanach‖) / 4)
    (constant := 8 * contourCauchyParameterOperatorConstant outerRadius /
      (innerRadius - ‖data - standardCircleBanach‖) ^ 2)
    (div_pos (sub_pos.mpr near) (by norm_num))
    (fun increment increment_small =>
      contourCauchyDerivativeDensityCLM_remainder_bound data increment near gap small increment_small)

theorem differentiableAt_extendedContourCauchyDerivativeDensityCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    DifferentiableAt ℂ extendedContourCauchyDerivativeDensityCLM data :=
  HasFDerivAt.differentiableAt (𝕜 := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (f := extendedContourCauchyDerivativeDensityCLM)
    (f' := contourCauchyDerivativeDensitySecondCLM data near gap small) (x := data)
    (hasFDerivAt_extendedContourCauchyDerivativeDensityCLM data near gap small)

end

end EulerNonuniqueness.Paper
