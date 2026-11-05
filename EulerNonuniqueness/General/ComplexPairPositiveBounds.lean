import EulerNonuniqueness.General.ComplexPairExtensionBounds

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairPositiveExtension_sub (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (first second : Space →L[ℝ] Space) :
    complexPairPositiveExtension conjugate antilinear first - complexPairPositiveExtension conjugate antilinear second =
      complexPairPositiveExtension conjugate antilinear (first - second) := by
  unfold complexPairPositiveExtension
  rw [smul_sub Complex.I first second, ← complexPairExtension_sub, ← complexPairExtension_sub]
  apply ContinuousLinearMap.ext
  intro pair
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply]
  module

theorem complexPairPositiveExtension_norm_le (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (operator : Space →L[ℝ] Space) :
    ‖complexPairPositiveExtension conjugate antilinear operator‖ ≤
      (‖complexPairEmbedding conjugate‖ *
        (‖complexPairReal conjugate‖ + ‖complexPairImaginary conjugate‖)) * ‖operator‖ := by
  have first := complexPairExtension_norm_le conjugate antilinear operator
  have second := complexPairExtension_norm_le conjugate antilinear (Complex.I • operator)
  have imaginaryBound : ‖Complex.I • operator‖ ≤ ‖operator‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro vector
    change ‖Complex.I • operator vector‖ ≤ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact operator.le_opNorm vector
  have secondBound := second.trans (mul_le_mul_of_nonneg_left imaginaryBound (by positivity))
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro pair
  change ‖(1 / 2 : ℂ) • (complexPairExtension conjugate antilinear operator pair -
    Complex.I • complexPairExtension conjugate antilinear (Complex.I • operator) pair)‖ ≤ _
  have halfNorm : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [norm_smul, halfNorm]
  have triangle := norm_sub_le (complexPairExtension conjugate antilinear operator pair)
    (Complex.I • complexPairExtension conjugate antilinear (Complex.I • operator) pair)
  rw [norm_smul, Complex.norm_I, one_mul] at triangle
  have firstApplied := (complexPairExtension conjugate antilinear operator).le_opNorm pair
  have secondApplied := (complexPairExtension conjugate antilinear (Complex.I • operator)).le_opNorm pair
  have firstFinal := firstApplied.trans (mul_le_mul_of_nonneg_right first (norm_nonneg pair))
  have secondFinal := secondApplied.trans (mul_le_mul_of_nonneg_right secondBound (norm_nonneg pair))
  nlinarith

theorem complexPairPositiveExtension_lipschitz (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector) :
    LipschitzWith (‖complexPairEmbedding conjugate‖₊ *
        (‖complexPairReal conjugate‖₊ + ‖complexPairImaginary conjugate‖₊))
      (complexPairPositiveExtension conjugate antilinear) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm, complexPairPositiveExtension_sub]
  exact complexPairPositiveExtension_norm_le conjugate antilinear (first - second)

end EulerNonuniqueness.General
