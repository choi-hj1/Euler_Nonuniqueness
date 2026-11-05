import EulerNonuniqueness.Section3.ContourSecondVariationDensityCLM
import EulerNonuniqueness.Section3.ContourSecondVariationDifference
import EulerNonuniqueness.Section3.ComplexOperatorUnitBound

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance secondOperatorLipHolderModule : Module ℂ PeriodicHolderHalf := Submodule.module complexPeriodicHolderGraph
local instance secondOperatorLipHolderSpace : NormedSpace ℂ PeriodicHolderHalf := Submodule.normedSpace complexPeriodicHolderGraph
local instance secondOperatorLipC1Module : Module ℂ PeriodicC1HolderHalf := Submodule.module complexPeriodicC1HolderGraph
local instance secondOperatorLipC1Space : NormedSpace ℂ PeriodicC1HolderHalf := Submodule.normedSpace complexPeriodicC1HolderGraph
local instance secondOperatorLipGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondOperatorLipModule : Module ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf) (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance secondOperatorLipSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondOperatorLipDoubleGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondOperatorLipDoubleModule : Module ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance secondOperatorLipDoubleSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondOperatorLipDoubleUniformAdd : IsUniformAddGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  SeminormedAddCommGroup.to_isUniformAddGroup
    (E := PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
local instance secondOperatorLipDoubleTopologicalAdd : IsTopologicalAddGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  IsUniformAddGroup.to_topologicalAddGroup
local instance secondOperatorLipDoubleContinuousAdd : ContinuousAdd
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  (inferInstance : IsTopologicalAddGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)).toContinuousAdd
local instance secondOperatorLipDensityGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondOperatorLipDensitySub : Sub
    (PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.sub (R := ℂ) (R₂ := ℂ) (M := PeriodicHolderHalf)
    (M₂ := PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem contourCauchySecondVariationCLM_difference_bound
    (initial final : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖contourCauchySecondVariationCLM initial density initialNear gap small -
      contourCauchySecondVariationCLM final density finalNear gap small‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ * ‖density‖ := by
  have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg (nonnegative.trans gap.le) small
  have boundNonnegative : 0 ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ * ‖density‖ := by positivity
  apply EulerNonuniqueness.General.complex_opNorm_le_of_unit_norm _ boundNonnegative
  intro first firstNorm
  apply EulerNonuniqueness.General.complex_opNorm_le_of_unit_norm _ boundNonnegative
  intro second secondNorm
  change ‖contourCauchySecondVariationCLM initial density initialNear gap small first second -
    contourCauchySecondVariationCLM final density finalNear gap small first second‖ ≤ _
  rw [contourCauchySecondVariationCLM_apply, contourCauchySecondVariationCLM_apply]
  have estimate := contourCauchySecondVariation_local_difference_bound initial final first second density
    nonnegative gap small initialNear.le finalNear.le
  rw [firstNorm, secondNorm] at estimate
  exact estimate.trans_eq (by ring)

theorem contourCauchySecondVariationDensityCLM_difference_bound
    (initial final : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (initialNear : ‖initial - standardCircleBanach‖ < innerRadius)
    (finalNear : ‖final - standardCircleBanach‖ < innerRadius) :
    ‖Sub.sub (α := PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
      (contourCauchySecondVariationDensityCLM initial initialNear gap small)
      (contourCauchySecondVariationDensityCLM final finalNear gap small)‖ ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ := by
  have parameterNonnegative := contourCauchyParameterOperatorConstant_nonneg (nonnegative.trans gap.le) small
  have boundNonnegative : 0 ≤
      (16 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius) ^ 2) *
        ‖initial - final‖ := by positivity
  apply EulerNonuniqueness.General.complex_opNorm_le_of_unit_norm _ boundNonnegative
  intro density densityNorm
  change ‖contourCauchySecondVariationCLM initial density initialNear gap small -
    contourCauchySecondVariationCLM final density finalNear gap small‖ ≤ _
  simpa only [densityNorm, mul_one] using
    contourCauchySecondVariationCLM_difference_bound initial final density nonnegative gap small initialNear finalNear

end

end EulerNonuniqueness.Paper
