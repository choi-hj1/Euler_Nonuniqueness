import EulerNonuniqueness.General.ComplexPairExtension
import EulerNonuniqueness.General.ComplexBilinearFromReal

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

def complexPairEmbeddedBilinear (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) : Space →L[ℝ] Space →L[ℝ] Space × Space :=
  ((ContinuousLinearMap.compL ℝ Space Space (Space × Space)) (complexPairEmbedding conjugate)).comp bilinear

theorem complexPairEmbeddedBilinear_apply (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (first second : Space) :
    complexPairEmbeddedBilinear conjugate bilinear first second = complexPairEmbedding conjugate (bilinear first second) := rfl

def complexPairBilinearRealExtension (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) :
    (Space × Space) →L[ℝ] (Space × Space) →L[ℝ] Space × Space :=
  let embedded := complexPairEmbeddedBilinear conjugate bilinear
  let realPart := complexPairReal conjugate
  let imaginaryPart := complexPairImaginary conjugate
  embedded.bilinearComp realPart realPart - embedded.bilinearComp imaginaryPart imaginaryPart +
    Complex.I • (embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart)

theorem complexPairBilinearRealExtension_apply (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (first second : Space × Space) :
    complexPairBilinearRealExtension conjugate bilinear first second =
      complexPairEmbedding conjugate (bilinear (complexPairReal conjugate first) (complexPairReal conjugate second)) -
      complexPairEmbedding conjugate (bilinear (complexPairImaginary conjugate first) (complexPairImaginary conjugate second)) +
      Complex.I • (complexPairEmbedding conjugate (bilinear (complexPairReal conjugate first) (complexPairImaginary conjugate second)) +
        complexPairEmbedding conjugate (bilinear (complexPairImaginary conjugate first) (complexPairReal conjugate second))) := rfl

theorem complexPairBilinearRealExtension_first_imaginary (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (first second : Space × Space) :
    complexPairBilinearRealExtension conjugate bilinear (Complex.I • first) second =
      Complex.I • complexPairBilinearRealExtension conjugate bilinear first second := by
  simp only [complexPairBilinearRealExtension_apply,
    complexPairReal_imaginary_smul conjugate antilinear, complexPairImaginary_imaginary_smul conjugate antilinear,
    map_neg, ContinuousLinearMap.neg_apply]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

theorem complexPairBilinearRealExtension_second_imaginary (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (first second : Space × Space) :
    complexPairBilinearRealExtension conjugate bilinear first (Complex.I • second) =
      Complex.I • complexPairBilinearRealExtension conjugate bilinear first second := by
  simp only [complexPairBilinearRealExtension_apply,
    complexPairReal_imaginary_smul conjugate antilinear, complexPairImaginary_imaginary_smul conjugate antilinear,
    map_neg]
  match_scalars <;> ring_nf <;> simp [Complex.I_sq]

def complexPairBilinearExtension (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) :
    (Space × Space) →L[ℂ] (Space × Space) →L[ℂ] Space × Space :=
  complexBilinearFromReal (complexPairBilinearRealExtension conjugate bilinear)
    (complexPairBilinearRealExtension_first_imaginary conjugate antilinear bilinear)
    (complexPairBilinearRealExtension_second_imaginary conjugate antilinear bilinear)

theorem complexPairBilinearExtension_embedding (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (first second : Space) :
    complexPairBilinearExtension conjugate antilinear bilinear
      (complexPairEmbedding conjugate first) (complexPairEmbedding conjugate second) =
      complexPairEmbedding conjugate (bilinear first second) := by
  change complexPairBilinearRealExtension conjugate bilinear
    (complexPairEmbedding conjugate first) (complexPairEmbedding conjugate second) = _
  rw [complexPairBilinearRealExtension_apply,
    complexPairReal_embedding conjugate involution, complexPairReal_embedding conjugate involution,
    complexPairImaginary_embedding conjugate involution, complexPairImaginary_embedding conjugate involution]
  simp only [map_zero, ContinuousLinearMap.zero_apply, sub_zero, add_zero, smul_zero]

end

end EulerNonuniqueness.General
