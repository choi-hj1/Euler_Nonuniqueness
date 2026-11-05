import EulerNonuniqueness.General.ComplexLinearFromReal
import Mathlib.Tactic.Module

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

def complexPairEmbedding (conjugate : Space →L[ℝ] Space) : Space →L[ℝ] Space × Space :=
  (ContinuousLinearMap.id ℝ Space).prod conjugate

def complexPairReal (conjugate : Space →L[ℝ] Space) : (Space × Space) →L[ℝ] Space :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.fst ℝ Space Space + conjugate.comp (ContinuousLinearMap.snd ℝ Space Space))

def complexPairImaginary (conjugate : Space →L[ℝ] Space) : (Space × Space) →L[ℝ] Space :=
  (-Complex.I / 2 : ℂ) • (ContinuousLinearMap.fst ℝ Space Space - conjugate.comp (ContinuousLinearMap.snd ℝ Space Space))

theorem complexPairReal_imaginary_smul (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (pair : Space × Space) :
    complexPairReal conjugate (Complex.I • pair) = -complexPairImaginary conjugate pair := by
  change (1 / 2 : ℂ) • (Complex.I • pair.1 + conjugate (Complex.I • pair.2)) =
    -((-Complex.I / 2 : ℂ) • (pair.1 - conjugate pair.2))
  rw [antilinear]
  simp only [Complex.star_def, map_neg, map_one, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem complexPairImaginary_imaginary_smul (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (pair : Space × Space) :
    complexPairImaginary conjugate (Complex.I • pair) = complexPairReal conjugate pair := by
  change (-Complex.I / 2 : ℂ) • (Complex.I • pair.1 - conjugate (Complex.I • pair.2)) =
    (1 / 2 : ℂ) • (pair.1 + conjugate pair.2)
  rw [antilinear]
  simp only [Complex.star_def, Complex.conj_I]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

def complexPairRealExtension (conjugate : Space →L[ℝ] Space) (operator : Space →L[ℝ] Space) :
    (Space × Space) →L[ℝ] Space × Space :=
  (complexPairEmbedding conjugate).comp (operator.comp (complexPairReal conjugate)) +
    Complex.I • (complexPairEmbedding conjugate).comp (operator.comp (complexPairImaginary conjugate))

theorem complexPairRealExtension_imaginary_smul (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (operator : Space →L[ℝ] Space) (pair : Space × Space) :
    complexPairRealExtension conjugate operator (Complex.I • pair) =
      Complex.I • complexPairRealExtension conjugate operator pair := by
  simp only [complexPairRealExtension, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, complexPairReal_imaginary_smul conjugate antilinear,
    complexPairImaginary_imaginary_smul conjugate antilinear, map_neg]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

def complexPairExtension (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (operator : Space →L[ℝ] Space) : (Space × Space) →L[ℂ] Space × Space :=
  complexLinearFromReal (complexPairRealExtension conjugate operator)
    (complexPairRealExtension_imaginary_smul conjugate antilinear operator)

theorem complexPairReal_embedding (conjugate : Space →L[ℝ] Space)
    (involution : ∀ vector, conjugate (conjugate vector) = vector) (vector : Space) :
    complexPairReal conjugate (complexPairEmbedding conjugate vector) = vector := by
  change (1 / 2 : ℂ) • (vector + conjugate (conjugate vector)) = vector
  rw [involution]
  module

theorem complexPairImaginary_embedding (conjugate : Space →L[ℝ] Space)
    (involution : ∀ vector, conjugate (conjugate vector) = vector) (vector : Space) :
    complexPairImaginary conjugate (complexPairEmbedding conjugate vector) = 0 := by
  change (-Complex.I / 2 : ℂ) • (vector - conjugate (conjugate vector)) = 0
  rw [involution, sub_self, smul_zero]

theorem complexPairExtension_embedding (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space) (vector : Space) :
    complexPairExtension conjugate antilinear operator (complexPairEmbedding conjugate vector) =
      complexPairEmbedding conjugate (operator vector) := by
  change complexPairEmbedding conjugate (operator (complexPairReal conjugate (complexPairEmbedding conjugate vector))) +
    Complex.I • complexPairEmbedding conjugate
      (operator (complexPairImaginary conjugate (complexPairEmbedding conjugate vector))) = _
  rw [complexPairReal_embedding conjugate involution, complexPairImaginary_embedding conjugate involution,
    map_zero, map_zero, smul_zero, add_zero]

end

end EulerNonuniqueness.General
