import EulerNonuniqueness.Section3.ContourSecondVariationDensity

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance secondDensityHolderSpace : NormedSpace ℂ PeriodicHolderHalf := Submodule.normedSpace complexPeriodicHolderGraph
local instance secondDensityC1Space : NormedSpace ℂ PeriodicC1HolderHalf := Submodule.normedSpace complexPeriodicC1HolderGraph
local instance secondDensityOperatorGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondDensityOperatorModule : Module ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance secondDensityOperatorSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondDensityDoubleOperatorGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondDensityDoubleOperatorModule : Module ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.module (R := ℂ) (R₃ := ℂ) (S₃ := ℂ) (M := PeriodicC1HolderHalf)
    (M₃ := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₃ := RingHom.id ℂ)
local instance secondDensityDoubleOperatorSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ) (E := PeriodicC1HolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

theorem contourCauchySecondVariationCLM_norm_bound (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    ‖contourCauchySecondVariationCLM data density near gap small‖ ≤
      (2 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius)) * ‖density‖ := by
  have parameter_nonnegative := contourCauchyParameterOperatorConstant_nonneg
    ((norm_nonneg _).trans (near.trans gap).le) small
  have constant_nonnegative : 0 ≤ (2 * contourCauchyParameterOperatorConstant outerRadius /
      (outerRadius - innerRadius)) * ‖density‖ :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) parameter_nonnegative) (sub_nonneg.mpr gap.le)) (norm_nonneg density)
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (contourCauchySecondVariationCLM data density near gap small) constant_nonnegative
  intro first
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (contourCauchySecondVariationCLM data density near gap small first)
    (mul_nonneg constant_nonnegative (norm_nonneg first))
  intro second
  rw [contourCauchySecondVariationCLM_apply]
  exact (contourCauchySecondVariation_norm_bound data first second density near gap small).trans_eq (by ring)

def contourCauchySecondVariationDensityLinearMap (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    PeriodicHolderHalf →ₗ[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf where
  toFun density := contourCauchySecondVariationCLM data density near gap small
  map_add' initial final := by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    exact contourCauchySecondVariation_add_density data first second initial final (near.trans (gap.trans small))
  map_smul' scalar density := by
    apply ContinuousLinearMap.ext
    intro first
    apply ContinuousLinearMap.ext
    intro second
    exact contourCauchySecondVariation_smul_density data first second density (near.trans (gap.trans small)) scalar

def contourCauchySecondVariationDensityCLM (data : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    PeriodicHolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous (𝕜 := ℂ) (𝕜₂ := ℂ) (E := PeriodicHolderHalf)
    (F := PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf)
    (contourCauchySecondVariationDensityLinearMap data near gap small)
    (2 * contourCauchyParameterOperatorConstant outerRadius / (outerRadius - innerRadius))
    (fun density => contourCauchySecondVariationCLM_norm_bound data density near gap small)

theorem contourCauchySecondVariationDensityCLM_apply (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariationDensityCLM data near gap small density first second =
      contourCauchySecondVariation data first second density := rfl

end

end EulerNonuniqueness.Paper
