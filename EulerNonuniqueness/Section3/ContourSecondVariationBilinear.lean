import EulerNonuniqueness.Section3.ContourCauchyBilinearAlgebra
import EulerNonuniqueness.Section3.ContourCauchyBilinearTaylor
import EulerNonuniqueness.Section3.ComplexHolderInstances

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance secondVariationBilinearHolderComplexSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph
local instance secondVariationBilinearC1ComplexSpace : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph
local instance secondVariationBilinearOperatorGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance secondVariationBilinearOperatorSpace : NormedSpace ℂ
    (PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

def contourCauchySecondVariationLinearMap (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →ₗ[ℂ] PeriodicC1HolderHalf →ₗ[ℂ] PeriodicHolderHalf :=
  LinearMap.mk₂ ℂ (fun first second => contourCauchySecondVariation data first second density)
    (fun first second third => contourCauchySecondVariation_add_left data first second third density small)
    (fun scalar first second => contourCauchySecondVariation_smul_left data first second density small scalar)
    (fun first second third => contourCauchySecondVariation_add_right data first second third density small)
    (fun scalar first second => contourCauchySecondVariation_smul_right data first second density small scalar)

def contourCauchySecondVariationCLM (data : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous₂ (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf) (G := PeriodicHolderHalf)
    (contourCauchySecondVariationLinearMap data density (near.trans (gap.trans small)))
    (2 * contourCauchyParameterOperatorConstant outerRadius * ‖density‖ / (outerRadius - innerRadius))
    (fun first second => contourCauchySecondVariation_norm_bound data first second density near gap small)

theorem contourCauchySecondVariationCLM_apply (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariationCLM data density near gap small first second =
      contourCauchySecondVariation data first second density := rfl

end

end EulerNonuniqueness.Paper
