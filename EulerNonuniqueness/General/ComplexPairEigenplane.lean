import EulerNonuniqueness.General.ComplexPairExtension
import Mathlib.Tactic.Module

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPair_positive_span (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (vector : Space) : (vector, (0 : Space)) =
      (1 / 2 : ℂ) • complexPairEmbedding conjugate vector +
        (-Complex.I / 2 : ℂ) • complexPairEmbedding conjugate (Complex.I • vector) := by
  apply Prod.ext
  · change vector = (1 / 2 : ℂ) • vector + (-Complex.I / 2 : ℂ) • (Complex.I • vector)
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num
  · change (0 : Space) = (1 / 2 : ℂ) • conjugate vector +
      (-Complex.I / 2 : ℂ) • conjugate (Complex.I • vector)
    rw [antilinear]
    simp only [Complex.star_def, Complex.conj_I]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem complexPairExtension_positive_eigenplane (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space) (vector : Space)
    (imaginary : operator (Complex.I • vector) = Complex.I • operator vector) :
    complexPairExtension conjugate antilinear operator (vector, 0) = (operator vector, 0) := by
  have span := congrArg (complexPairExtension conjugate antilinear operator)
    (complexPair_positive_span conjugate antilinear vector)
  rw [map_add, map_smul, map_smul,
    complexPairExtension_embedding conjugate antilinear involution,
    complexPairExtension_embedding conjugate antilinear involution, imaginary] at span
  exact span.trans (complexPair_positive_span conjugate antilinear (operator vector)).symm

end

end EulerNonuniqueness.General
