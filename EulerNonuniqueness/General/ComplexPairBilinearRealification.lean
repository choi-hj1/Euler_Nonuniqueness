import EulerNonuniqueness.General.ComplexPairBilinearExtension
import EulerNonuniqueness.General.ComplexPairRealification

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairReal_bilinear_physical_left (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (direction : Space) (pair : Space × Space) :
    complexPairReal conjugate (complexPairBilinearExtension conjugate antilinear bilinear
      (complexPairEmbedding conjugate direction) pair) = bilinear direction (complexPairReal conjugate pair) := by
  change complexPairReal conjugate (complexPairBilinearRealExtension conjugate bilinear
    (complexPairEmbedding conjugate direction) pair) = _
  rw [complexPairBilinearRealExtension_apply, complexPairReal_embedding conjugate involution,
    complexPairImaginary_embedding conjugate involution]
  simp only [map_zero, ContinuousLinearMap.zero_apply, sub_zero, add_zero]
  rw [map_add, complexPairReal_embedding conjugate involution,
    complexPairReal_imaginary_smul conjugate antilinear,
    complexPairImaginary_embedding conjugate involution, neg_zero, add_zero]

theorem complexPairReal_scaled_bilinear_physical_left (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (direction : Space) (pair : Space × Space) (coefficient : ℂ) :
    (2 : ℝ) • complexPairReal conjugate (coefficient •
      complexPairBilinearExtension conjugate antilinear bilinear (complexPairEmbedding conjugate direction) pair) =
      bilinear direction ((2 : ℝ) • complexPairReal conjugate (coefficient • pair)) := by
  have scalarIdentity : coefficient •
      complexPairBilinearExtension conjugate antilinear bilinear (complexPairEmbedding conjugate direction) pair =
      complexPairBilinearExtension conjugate antilinear bilinear
        (complexPairEmbedding conjugate direction) (coefficient • pair) :=
    ((complexPairBilinearExtension conjugate antilinear bilinear
      (complexPairEmbedding conjugate direction)).map_smul coefficient pair).symm
  rw [scalarIdentity, complexPairReal_bilinear_physical_left conjugate antilinear involution]
  exact ((bilinear direction).map_smul (2 : ℝ) _).symm

end

end EulerNonuniqueness.General
