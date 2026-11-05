import Mathlib.Analysis.NormedSpace.OperatorNorm.Bilinear
import Mathlib.Analysis.Complex.Basic

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℂ Space]

def forcingLinearCoefficient (derivative : Space →L[ℂ] Space)
    (quadratic : Space →L[ℂ] Space →L[ℂ] Space) (primitive : Space) : Space →L[ℂ] Space :=
  derivative + (2 : ℂ) • quadratic.flip primitive

theorem forcingLinearCoefficient_weighted (derivative : Space →L[ℂ] Space)
    (quadratic : Space →L[ℂ] Space →L[ℂ] Space) (primitive : Space)
    (transform : Space →L[ℂ] Space) (weight : ℂ)
    (derivativeEquivariant : transform.comp derivative = weight • derivative.comp transform)
    (quadraticEquivariant : ∀ first second, quadratic (transform first) (transform second) = transform (quadratic first second))
    (primitiveEigen : transform primitive = weight • primitive) (direction : Space) :
    transform (forcingLinearCoefficient derivative quadratic primitive direction) =
      weight • forcingLinearCoefficient derivative quadratic primitive (transform direction) := by
  have derivativeIdentity := congrArg (fun operator : Space →L[ℂ] Space => operator direction) derivativeEquivariant
  have quadraticIdentity := quadraticEquivariant direction primitive
  rw [primitiveEigen, map_smul] at quadraticIdentity
  change transform (derivative direction + (2 : ℂ) • quadratic direction primitive) =
    weight • (derivative (transform direction) + (2 : ℂ) • quadratic (transform direction) primitive)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] at derivativeIdentity
  rw [map_add, map_smul, derivativeIdentity, ← quadraticIdentity, smul_add]
  exact congrArg (fun remainder : Space => weight • derivative (transform direction) + remainder)
    (smul_comm (2 : ℂ) weight (quadratic (transform direction) primitive))

end

end EulerNonuniqueness.General
