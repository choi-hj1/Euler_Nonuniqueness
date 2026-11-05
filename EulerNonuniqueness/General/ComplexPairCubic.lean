import EulerNonuniqueness.General.ComplexPairUniqueness

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairExtension_cubic (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space)
    (cubic : ∀ vector, operator (operator (operator vector)) = (-1 / 4 : ℝ) • operator vector)
    (pair : Space × Space) :
    complexPairExtension conjugate antilinear operator
      (complexPairExtension conjugate antilinear operator
        (complexPairExtension conjugate antilinear operator pair)) =
      (-1 / 4 : ℂ) • complexPairExtension conjugate antilinear operator pair := by
  let extension := complexPairExtension conjugate antilinear operator
  have physical (vector : Space) : extension (complexPairEmbedding conjugate vector) =
      complexPairEmbedding conjugate (operator vector) :=
    complexPairExtension_embedding conjugate antilinear involution operator vector
  have equality : extension.comp (extension.comp extension) = (-1 / 4 : ℂ) • extension := by
    apply complexPair_linear_ext conjugate antilinear involution
    intro vector
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, physical, cubic, map_smul]
    apply Prod.ext <;> change (-1 / 4 : ℝ) • _ = (-1 / 4 : ℂ) • _ <;>
      simpa only [map_div₀, map_neg, map_one, map_ofNat] using
        (algebraMap_smul ℂ (-1 / 4 : ℝ) _).symm
  exact congrArg (fun linear : (Space × Space) →L[ℂ] Space × Space => linear pair) equality

end

end EulerNonuniqueness.General
