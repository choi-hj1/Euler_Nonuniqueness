import EulerNonuniqueness.General.ContinuousSubPreservingRegularity
import EulerNonuniqueness.General.ComplexPairPositiveBounds
import EulerNonuniqueness.General.ComplexPairBilinearLipschitz

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

local instance pairExtensionOperatorRealSpace : NormedSpace ℝ ((Space × Space) →L[ℂ] Space × Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := Space × Space) (F := Space × Space) (σ₁₂ := RingHom.id ℂ)

local instance pairExtensionBilinearRealSpace : NormedSpace ℝ
    ((Space × Space) →L[ℂ] (Space × Space) →L[ℂ] Space × Space) :=
  ContinuousLinearMap.toNormedSpace (𝕜 := ℂ) (𝕜₂ := ℂ) (𝕜' := ℝ)
    (E := Space × Space) (F := (Space × Space) →L[ℂ] Space × Space) (σ₁₂ := RingHom.id ℂ)

theorem complexPairExtension_hasLipschitzDerivativeNear
    (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (point : Space →L[ℝ] Space) :
    HasLipschitzDerivativeNear (complexPairExtension conjugate antilinear) point :=
  hasLipschitzDerivativeNear_of_sub_preserving _
    (fun first second => (complexPairExtension_sub conjugate antilinear first second).symm)
    (complexPairExtension_lipschitz conjugate antilinear).continuous point

theorem complexPairPositiveExtension_hasLipschitzDerivativeNear
    (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (point : Space →L[ℝ] Space) :
    HasLipschitzDerivativeNear (complexPairPositiveExtension conjugate antilinear) point :=
  hasLipschitzDerivativeNear_of_sub_preserving _
    (fun first second => (complexPairPositiveExtension_sub conjugate antilinear first second).symm)
    (complexPairPositiveExtension_lipschitz conjugate antilinear).continuous point

theorem complexPairBilinearExtension_hasLipschitzDerivativeNear
    (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (point : Space →L[ℝ] Space →L[ℝ] Space) :
    HasLipschitzDerivativeNear (complexPairBilinearExtension conjugate antilinear) point :=
  hasLipschitzDerivativeNear_of_sub_preserving _
    (fun first second => (complexPairBilinearExtension_sub conjugate antilinear first second).symm)
    (complexPairBilinearExtension_lipschitz conjugate antilinear).continuous point

end EulerNonuniqueness.General
