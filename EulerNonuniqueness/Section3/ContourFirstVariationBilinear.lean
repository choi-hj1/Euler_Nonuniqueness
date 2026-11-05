import EulerNonuniqueness.Section3.ContourCauchyBilinearAlgebra
import EulerNonuniqueness.Section3.ComplexHolderInstances

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance firstVariationBilinearHolderSpace : NormedSpace ℂ PeriodicHolderHalf :=
  Submodule.normedSpace complexPeriodicHolderGraph
local instance firstVariationBilinearC1Space : NormedSpace ℂ PeriodicC1HolderHalf :=
  Submodule.normedSpace complexPeriodicC1HolderGraph
local instance firstVariationBilinearOperatorGroup : NormedAddCommGroup
    (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℂ) (𝕜₂ := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)
local instance firstVariationBilinearOperatorSpace : NormedSpace ℂ
    (PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℂ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℂ)

def contourCauchyFirstVariationLinearMap (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →ₗ[ℂ] PeriodicHolderHalf →ₗ[ℂ] PeriodicHolderHalf :=
  LinearMap.mk₂ ℂ (fun direction density => contourCauchyDirectionalDerivative data direction density)
    (fun first second density => contourCauchyDirectionalDerivative_add data first second density small)
    (fun scalar direction density => contourCauchyDirectionalDerivative_smul data direction density small scalar)
    (fun direction first second => contourCauchyDirectionalDerivative_add_density data direction first second small)
    (fun scalar direction density => contourCauchyDirectionalDerivative_smul_density data direction density small scalar)

def contourCauchyFirstVariationCLM (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    PeriodicC1HolderHalf →L[ℂ] PeriodicHolderHalf →L[ℂ] PeriodicHolderHalf :=
  LinearMap.mkContinuous₂ (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜₃ := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
    (contourCauchyFirstVariationLinearMap data (near.trans small))
    (contourCauchyParameterOperatorConstant radius)
    (fun direction density => (contourCauchyDirectionalDerivative_norm_bound data direction density near small).trans_eq (by ring))

theorem contourCauchyFirstVariationCLM_apply (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourCauchyFirstVariationCLM data near small direction density =
      contourCauchyDirectionalDerivative data direction density := rfl

end

end EulerNonuniqueness.Paper
