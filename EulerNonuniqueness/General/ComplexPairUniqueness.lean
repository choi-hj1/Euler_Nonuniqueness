import EulerNonuniqueness.General.ComplexPairBilinearExtension

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPair_reconstruct (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector) (pair : Space × Space) :
    pair = complexPairEmbedding conjugate (complexPairReal conjugate pair) +
      Complex.I • complexPairEmbedding conjugate (complexPairImaginary conjugate pair) := by
  apply Prod.ext
  · change pair.1 = (1 / 2 : ℂ) • (pair.1 + conjugate pair.2) +
      Complex.I • ((-Complex.I / 2 : ℂ) • (pair.1 - conjugate pair.2))
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num
  · change pair.2 = conjugate ((1 / 2 : ℂ) • (pair.1 + conjugate pair.2)) +
      Complex.I • conjugate ((-Complex.I / 2 : ℂ) • (pair.1 - conjugate pair.2))
    rw [antilinear, antilinear, map_add, map_sub, involution]
    simp only [Complex.star_def, map_div₀, map_one, map_ofNat, map_neg, Complex.conj_I]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> norm_num

theorem complexPair_linear_ext (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (first second : (Space × Space) →L[ℂ] Target)
    (physical : ∀ vector, first (complexPairEmbedding conjugate vector) = second (complexPairEmbedding conjugate vector)) :
    first = second := by
  apply ContinuousLinearMap.ext
  intro pair
  have reconstruct := complexPair_reconstruct conjugate antilinear involution pair
  calc
    first pair = first (complexPairEmbedding conjugate (complexPairReal conjugate pair)) +
        Complex.I • first (complexPairEmbedding conjugate (complexPairImaginary conjugate pair)) := by
      conv_lhs => rw [reconstruct]
      rw [map_add, map_smul]
    _ = second (complexPairEmbedding conjugate (complexPairReal conjugate pair)) +
        Complex.I • second (complexPairEmbedding conjugate (complexPairImaginary conjugate pair)) := by rw [physical, physical]
    _ = second pair := by rw [← map_smul, ← map_add, ← reconstruct]

theorem complexPair_bilinear_ext (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (involution : ∀ vector, conjugate (conjugate vector) = vector)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (first second : (Space × Space) →L[ℂ] (Space × Space) →L[ℂ] Target)
    (physical : ∀ firstVector secondVector,
      first (complexPairEmbedding conjugate firstVector) (complexPairEmbedding conjugate secondVector) =
      second (complexPairEmbedding conjugate firstVector) (complexPairEmbedding conjugate secondVector)) :
    first = second := by
  have physicalFirst (vector : Space) : first (complexPairEmbedding conjugate vector) =
      second (complexPairEmbedding conjugate vector) :=
    complexPair_linear_ext conjugate antilinear involution _ _ (physical vector)
  apply ContinuousLinearMap.ext
  intro firstPair
  apply ContinuousLinearMap.ext
  intro secondPair
  have reconstruct := complexPair_reconstruct conjugate antilinear involution firstPair
  calc
    first firstPair secondPair = first (complexPairEmbedding conjugate (complexPairReal conjugate firstPair)) secondPair +
        Complex.I • first (complexPairEmbedding conjugate (complexPairImaginary conjugate firstPair)) secondPair := by
      conv_lhs => rw [reconstruct]
      rw [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    _ = second (complexPairEmbedding conjugate (complexPairReal conjugate firstPair)) secondPair +
        Complex.I • second (complexPairEmbedding conjugate (complexPairImaginary conjugate firstPair)) secondPair := by
      rw [physicalFirst, physicalFirst]
    _ = second firstPair secondPair := by
      conv_rhs => rw [reconstruct]
      rw [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]

end

end EulerNonuniqueness.General
