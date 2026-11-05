import EulerNonuniqueness.General.ComplexPairExtension

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairReal_extension (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space) (pair : Space × Space) :
    complexPairReal conjugate (complexPairExtension conjugate antilinear operator pair) =
      operator (complexPairReal conjugate pair) := by
  change complexPairReal conjugate (complexPairEmbedding conjugate (operator (complexPairReal conjugate pair)) +
      Complex.I • complexPairEmbedding conjugate (operator (complexPairImaginary conjugate pair))) = _
  rw [map_add, complexPairReal_embedding conjugate involution,
    complexPairReal_imaginary_smul conjugate antilinear,
    complexPairImaginary_embedding conjugate involution, neg_zero, add_zero]

theorem complexPairReal_positive (conjugate : Space →L[ℝ] Space) (vector : Space) :
    (2 : ℝ) • complexPairReal conjugate (vector, 0) = vector := by
  change (2 : ℝ) • ((1 / 2 : ℂ) • (vector + conjugate 0)) = vector
  rw [map_zero, add_zero, ← algebraMap_smul ℂ (2 : ℝ), smul_smul]
  norm_num

theorem complexPairReal_homological_equation (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    (operator : Space →L[ℝ] Space) (frequency scalar : ℂ)
    (correction numerator : Space × Space)
    (equation : frequency • correction - complexPairExtension conjugate antilinear operator correction = numerator) :
    (2 : ℝ) • complexPairReal conjugate ((scalar * frequency) • correction) -
      operator ((2 : ℝ) • complexPairReal conjugate (scalar • correction)) =
      (2 : ℝ) • complexPairReal conjugate (scalar • numerator) := by
  have scaled := congrArg (fun value : Space × Space => (2 : ℝ) • complexPairReal conjugate (scalar • value)) equation
  simp only [smul_sub, map_sub, smul_smul] at scaled
  have commutes : (2 : ℝ) • complexPairReal conjugate
      (scalar • complexPairExtension conjugate antilinear operator correction) =
      operator ((2 : ℝ) • complexPairReal conjugate (scalar • correction)) := by
    calc
      _ = (2 : ℝ) • complexPairReal conjugate
          (complexPairExtension conjugate antilinear operator (scalar • correction)) :=
        congrArg (fun pair : Space × Space => (2 : ℝ) • complexPairReal conjugate pair)
          ((complexPairExtension conjugate antilinear operator).map_smul scalar correction).symm
      _ = (2 : ℝ) • operator (complexPairReal conjugate (scalar • correction)) := by
        rw [complexPairReal_extension conjugate antilinear involution]
      _ = _ := (operator.map_smul (2 : ℝ) _).symm
  rw [commutes] at scaled
  exact scaled

end

end EulerNonuniqueness.General
