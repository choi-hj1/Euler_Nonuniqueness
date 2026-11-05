import EulerNonuniqueness.General.ComplexPairBilinearExtension
import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space]
  [NormedSpace ℂ Space] [NormedSpace ℝ Space]
  [IsScalarTower ℝ ℂ Space] [SMulCommClass ℝ ℂ Space]

theorem complexPairEmbeddedBilinear_norm_le (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖complexPairEmbeddedBilinear conjugate bilinear‖ ≤ ‖complexPairEmbedding conjugate‖ * ‖bilinear‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro first second
  rw [complexPairEmbeddedBilinear_apply]
  calc
    _ ≤ ‖complexPairEmbedding conjugate‖ * ‖bilinear first second‖ :=
      (complexPairEmbedding conjugate).le_opNorm _
    _ ≤ ‖complexPairEmbedding conjugate‖ * (‖bilinear‖ * ‖first‖ * ‖second‖) :=
      mul_le_mul_of_nonneg_left (bilinear.le_opNorm₂ _ _) (norm_nonneg _)
    _ = _ := by ring

theorem pairBilinearComp_norm_le (bilinear : Space →L[ℝ] Space →L[ℝ] Space × Space)
    (firstMap secondMap : (Space × Space) →L[ℝ] Space) :
    ‖bilinear.bilinearComp firstMap secondMap‖ ≤ ‖bilinear‖ * ‖firstMap‖ * ‖secondMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro first second
  change ‖bilinear (firstMap first) (secondMap second)‖ ≤ _
  calc
    _ ≤ ‖bilinear‖ * ‖firstMap first‖ * ‖secondMap second‖ := bilinear.le_opNorm₂ _ _
    _ ≤ ‖bilinear‖ * (‖firstMap‖ * ‖first‖) * (‖secondMap‖ * ‖second‖) := by
      gcongr
      · exact firstMap.le_opNorm first
      · exact secondMap.le_opNorm second
    _ = _ := by ring

theorem complexPairBilinearRealExtension_norm_le (conjugate : Space →L[ℝ] Space)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖complexPairBilinearRealExtension conjugate bilinear‖ ≤
      (‖complexPairEmbedding conjugate‖ *
        (‖complexPairReal conjugate‖ + ‖complexPairImaginary conjugate‖) ^ 2) * ‖bilinear‖ := by
  let embedded := complexPairEmbeddedBilinear conjugate bilinear
  let realPart := complexPairReal conjugate
  let imaginaryPart := complexPairImaginary conjugate
  have first := pairBilinearComp_norm_le embedded realPart realPart
  have second := pairBilinearComp_norm_le embedded imaginaryPart imaginaryPart
  have third := pairBilinearComp_norm_le embedded realPart imaginaryPart
  have fourth := pairBilinearComp_norm_le embedded imaginaryPart realPart
  have embeddedBound := complexPairEmbeddedBilinear_norm_le conjugate bilinear
  have imaginaryBound : ‖Complex.I • (embedded.bilinearComp realPart imaginaryPart +
      embedded.bilinearComp imaginaryPart realPart)‖ ≤
      ‖embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart‖ := by
    apply ContinuousLinearMap.opNorm_le_bound₂ _ (C := ‖embedded.bilinearComp realPart imaginaryPart +
      embedded.bilinearComp imaginaryPart realPart‖)
      (norm_nonneg (embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart))
    intro first second
    change ‖Complex.I • ((embedded.bilinearComp realPart imaginaryPart +
      embedded.bilinearComp imaginaryPart realPart) first second)‖ ≤ _
    rw [norm_smul, Complex.norm_I, one_mul]
    exact (embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart).le_opNorm₂ _ _
  change ‖embedded.bilinearComp realPart realPart - embedded.bilinearComp imaginaryPart imaginaryPart +
    Complex.I • (embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart)‖ ≤ _
  calc
    _ ≤ ‖embedded.bilinearComp realPart realPart‖ + ‖embedded.bilinearComp imaginaryPart imaginaryPart‖ +
        (‖embedded.bilinearComp realPart imaginaryPart‖ + ‖embedded.bilinearComp imaginaryPart realPart‖) := by
      refine (norm_add_le (embedded.bilinearComp realPart realPart - embedded.bilinearComp imaginaryPart imaginaryPart)
        (Complex.I • (embedded.bilinearComp realPart imaginaryPart + embedded.bilinearComp imaginaryPart realPart))).trans ?_
      exact add_le_add (norm_sub_le (embedded.bilinearComp realPart realPart) (embedded.bilinearComp imaginaryPart imaginaryPart))
        (imaginaryBound.trans (norm_add_le (embedded.bilinearComp realPart imaginaryPart)
          (embedded.bilinearComp imaginaryPart realPart)))
    _ ≤ ‖embedded‖ * (‖realPart‖ + ‖imaginaryPart‖) ^ 2 := by nlinarith
    _ ≤ (‖complexPairEmbedding conjugate‖ * ‖bilinear‖) * (‖realPart‖ + ‖imaginaryPart‖) ^ 2 :=
      mul_le_mul_of_nonneg_right embeddedBound (sq_nonneg _)
    _ = _ := by dsimp only [realPart, imaginaryPart]; ring

theorem complexPairBilinearExtension_norm_le (conjugate : Space →L[ℝ] Space)
    (antilinear : ∀ (scalar : ℂ) (vector : Space), conjugate (scalar • vector) = star scalar • conjugate vector)
    (bilinear : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖complexPairBilinearExtension conjugate antilinear bilinear‖ ≤
      (‖complexPairEmbedding conjugate‖ *
        (‖complexPairReal conjugate‖ + ‖complexPairImaginary conjugate‖) ^ 2) * ‖bilinear‖ := by
  apply le_trans _ (complexPairBilinearRealExtension_norm_le conjugate bilinear)
  exact ContinuousLinearMap.opNorm_le_bound₂ (complexPairBilinearExtension conjugate antilinear bilinear)
    (C := ‖complexPairBilinearRealExtension conjugate bilinear‖)
    (norm_nonneg (complexPairBilinearRealExtension conjugate bilinear))
    (fun first second => (complexPairBilinearRealExtension conjugate bilinear).le_opNorm₂ first second)

end EulerNonuniqueness.General
