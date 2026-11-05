import EulerNonuniqueness.Section3.ContourTangentInnerDerivative
import EulerNonuniqueness.Section3.ContourVelocityTangentJet

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance velocityTangentFrechetHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance velocityTangentFrechetC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance velocityTangentFrechetOperatorGroup : SeminormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toSeminormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)
local instance velocityTangentFrechetOperatorComplexSpace : NormedSpace ℂ (PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℝ) (𝕜₂ := ℝ) (𝕜' := ℂ)
    (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf) (σ₁₂ := RingHom.id ℝ)

def contourVelocityTangentDerivativeCLM (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℝ] PeriodicHolderHalf :=
  -(1 / (4 * Real.pi) : ℂ) •
    (holderProductRealCLM.precompR PeriodicC1HolderHalf (holderConjugate data.val.2)
        (contourHolderConjugateRealCLM.comp (contourTangentInnerDerivativeCLM data near small)) +
      holderProductRealCLM.precompL PeriodicC1HolderHalf
        (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM)
        (holderConjugate (contourTangentInner data)))

theorem contourVelocityTangentLinear_eq_derivative (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    contourVelocityTangentLinear data increment =
      contourVelocityTangentDerivativeCLM data near small increment := by
  unfold contourVelocityTangentLinear
  rw [contourTangentInnerLinear_eq_derivative data increment near small]
  rfl

theorem hasFDerivAt_holderContourVelocityTangent (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt holderContourVelocityTangent (contourVelocityTangentDerivativeCLM data near small) data := by
  have inner : HasFDerivAt contourTangentInner (contourTangentInnerDerivativeCLM data near small) data := by
    exact hasFDerivAt_contourTangentInner data near small
  have conjugate_inner : HasFDerivAt (fun current : PeriodicC1HolderHalf =>
      holderConjugate (contourTangentInner current))
      (contourHolderConjugateRealCLM.comp (contourTangentInnerDerivativeCLM data near small)) data := by
    exact HasFDerivAt.comp (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf) (G := PeriodicHolderHalf)
      (f := contourTangentInner) (g := holderConjugate) data
      (ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicHolderHalf)
        (F := PeriodicHolderHalf) contourHolderConjugateRealCLM) inner
  have tangent : HasFDerivAt (fun current : PeriodicC1HolderHalf => holderConjugate current.val.2)
      (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM) data := by
    exact ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf)
      (F := PeriodicHolderHalf) (contourHolderConjugateRealCLM.comp c1TangentHolderRealCLM)
  have product := ContinuousLinearMap.hasFDerivAt_of_bilinear (𝕜 := ℝ)
    (E := PeriodicHolderHalf) (F := PeriodicHolderHalf) (G := PeriodicHolderHalf) (G' := PeriodicC1HolderHalf)
    (f := fun current : PeriodicC1HolderHalf => holderConjugate current.val.2)
    (g := fun current : PeriodicC1HolderHalf => holderConjugate (contourTangentInner current))
    holderProductRealCLM tangent conjugate_inner
  exact HasFDerivAt.const_smul (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicHolderHalf)
    (R := ℂ) product (-(1 / (4 * Real.pi) : ℂ))

end

end EulerNonuniqueness.Paper
