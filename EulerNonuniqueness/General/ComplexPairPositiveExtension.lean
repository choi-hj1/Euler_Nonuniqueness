import EulerNonuniqueness.General.ComplexPairExtension
import Mathlib.Tactic.Module

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

def complexPairPositiveExtension (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (operator : Space →L[ℝ] Space) : (Space × Space) →L[ℂ] Space × Space :=
  (1 / 2 : ℂ) • (complexPairExtension conjugate antilinear operator -
    Complex.I • complexPairExtension conjugate antilinear (Complex.I • operator))

theorem complexPairPositiveExtension_embedding (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space) (vector : Space) :
    complexPairPositiveExtension conjugate antilinear operator (complexPairEmbedding conjugate vector) =
      (operator vector, 0) := by
  change (1 / 2 : ℂ) • (complexPairExtension conjugate antilinear operator (complexPairEmbedding conjugate vector) -
    Complex.I • complexPairExtension conjugate antilinear (Complex.I • operator) (complexPairEmbedding conjugate vector)) = _
  rw [complexPairExtension_embedding conjugate antilinear involution,
    complexPairExtension_embedding conjugate antilinear involution]
  apply Prod.ext
  · change (1 / 2 : ℂ) • (operator vector - Complex.I • (Complex.I • operator vector)) = operator vector
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num
  · change (1 / 2 : ℂ) • (conjugate (operator vector) - Complex.I • conjugate (Complex.I • operator vector)) = 0
    rw [antilinear]
    simp only [Complex.star_def, Complex.conj_I]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

end

end EulerNonuniqueness.General
