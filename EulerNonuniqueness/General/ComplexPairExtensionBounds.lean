import EulerNonuniqueness.General.ComplexPairPositiveExtension
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairExtension_sub (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (first second : Space →L[ℝ] Space) :
    complexPairExtension conjugate antilinear first - complexPairExtension conjugate antilinear second =
      complexPairExtension conjugate antilinear (first - second) := by
  apply ContinuousLinearMap.ext
  intro pair
  change complexPairEmbedding conjugate (first (complexPairReal conjugate pair)) +
      Complex.I • complexPairEmbedding conjugate (first (complexPairImaginary conjugate pair)) -
      (complexPairEmbedding conjugate (second (complexPairReal conjugate pair)) +
        Complex.I • complexPairEmbedding conjugate (second (complexPairImaginary conjugate pair))) =
    complexPairEmbedding conjugate ((first - second) (complexPairReal conjugate pair)) +
      Complex.I • complexPairEmbedding conjugate ((first - second) (complexPairImaginary conjugate pair))
  simp only [ContinuousLinearMap.sub_apply, map_sub, smul_sub]
  abel

theorem complexPairExtension_norm_le (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (operator : Space →L[ℝ] Space) :
    ‖complexPairExtension conjugate antilinear operator‖ ≤
      (‖complexPairEmbedding conjugate‖ *
        (‖complexPairReal conjugate‖ + ‖complexPairImaginary conjugate‖)) * ‖operator‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro pair
  change ‖complexPairEmbedding conjugate (operator (complexPairReal conjugate pair)) +
    Complex.I • complexPairEmbedding conjugate (operator (complexPairImaginary conjugate pair))‖ ≤ _
  calc
    _ ≤ ‖complexPairEmbedding conjugate (operator (complexPairReal conjugate pair))‖ +
        ‖Complex.I • complexPairEmbedding conjugate (operator (complexPairImaginary conjugate pair))‖ :=
      norm_add_le _ _
    _ ≤ ‖complexPairEmbedding conjugate‖ * (‖operator‖ * (‖complexPairReal conjugate‖ * ‖pair‖)) +
        ‖complexPairEmbedding conjugate‖ * (‖operator‖ * (‖complexPairImaginary conjugate‖ * ‖pair‖)) := by
      rw [norm_smul, Complex.norm_I, one_mul]
      apply add_le_add
      · exact ((complexPairEmbedding conjugate).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((operator.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((complexPairReal conjugate).le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
      · exact ((complexPairEmbedding conjugate).le_opNorm _).trans
          (mul_le_mul_of_nonneg_left ((operator.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left ((complexPairImaginary conjugate).le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
    _ = _ := by ring

theorem complexPairExtension_lipschitz (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector) :
    LipschitzWith (‖complexPairEmbedding conjugate‖₊ *
        (‖complexPairReal conjugate‖₊ + ‖complexPairImaginary conjugate‖₊))
      (complexPairExtension conjugate antilinear) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  rw [dist_eq_norm, dist_eq_norm, complexPairExtension_sub]
  exact complexPairExtension_norm_le conjugate antilinear (first - second)

end EulerNonuniqueness.General
