import EulerNonuniqueness.General.ComplexPairUniqueness

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairBilinearExtension_intertwines (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) (transform : Space →L[ℝ] Space)
    (equivariant : ∀ first second, bilinear (transform first) (transform second) = transform (bilinear first second))
    (first second : Space × Space) :
    complexPairBilinearExtension conjugate antilinear bilinear
      (complexPairExtension conjugate antilinear transform first)
      (complexPairExtension conjugate antilinear transform second) =
    complexPairExtension conjugate antilinear transform
      (complexPairBilinearExtension conjugate antilinear bilinear first second) := by
  let extended := complexPairBilinearExtension conjugate antilinear bilinear
  let symmetry := complexPairExtension conjugate antilinear transform
  let left := extended.bilinearComp symmetry symmetry
  let right := ((ContinuousLinearMap.compL ℂ (Space × Space) (Space × Space) (Space × Space)) symmetry).comp extended
  have identity : left = right := by
    apply complexPair_bilinear_ext conjugate antilinear involution
    intro firstVector secondVector
    change extended (symmetry (complexPairEmbedding conjugate firstVector))
      (symmetry (complexPairEmbedding conjugate secondVector)) =
      symmetry (extended (complexPairEmbedding conjugate firstVector) (complexPairEmbedding conjugate secondVector))
    dsimp only [extended, symmetry]
    rw [complexPairExtension_embedding conjugate antilinear involution,
      complexPairExtension_embedding conjugate antilinear involution,
      complexPairBilinearExtension_embedding conjugate antilinear involution,
      complexPairBilinearExtension_embedding conjugate antilinear involution,
      complexPairExtension_embedding conjugate antilinear involution, equivariant]
  exact congrArg (fun operator : (Space × Space) →L[ℂ] (Space × Space) →L[ℂ] Space × Space =>
    operator first second) identity

end

end EulerNonuniqueness.General
