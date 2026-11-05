import EulerNonuniqueness.Section6.HalfDiagonalCanonicalProfile
import EulerNonuniqueness.Section4.ReferenceSiblingSeparation

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem quadrupoleCentroidOffset_central_error (positive negative asymmetry : ℂ) (patch : Fin 4) :
    ‖quadrupoleCentroidOffset positive negative asymmetry patch -
      centrallySymmetricFourPoint positive negative patch‖ = ‖asymmetry‖ := by
  fin_cases patch <;> simp [quadrupoleCentroidOffset, centrallySymmetricFourPoint]

theorem normalized_quadrupoleCentroidOffset_error (positive negative asymmetry : ℂ)
    {length : ℝ} {rotation : ℂ} (lengthPositive : 0 < length) (rotationNorm : ‖rotation‖ = 1) :
    ‖(fun patch => ((length : ℂ) * rotation)⁻¹ * quadrupoleCentroidOffset positive negative asymmetry patch) -
      (fun patch => ((length : ℂ) * rotation)⁻¹ * centrallySymmetricFourPoint positive negative patch)‖ ≤ ‖asymmetry‖ / length := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) lengthPositive.le)).mpr
  intro patch
  simp only [Pi.sub_apply, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos lengthPositive, rotationNorm, mul_one, quadrupoleCentroidOffset_central_error]
  exact le_of_eq (by ring)

theorem halfDiagonalCanonicalProfile_reference (positive negative : ℂ)
    (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2) :
    (positive / (‖positive‖ : ℂ)) • halfDiagonalCanonicalProfile
      (‖positive‖ ^ 2 - ‖negative‖ ^ 2) (halfDiagonalShape positive negative) =
      centrallySymmetricFourPoint positive negative := by
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have positiveNonzero : positive ≠ 0 := norm_pos_iff.mp positiveNorm
  have rotationSelf : halfDiagonalMatchingRotation positive positive = 1 := by
    unfold halfDiagonalMatchingRotation
    exact div_self (div_ne_zero positiveNonzero (Complex.ofReal_ne_zero.mpr positiveNorm.ne'))
  have identity := halfDiagonalCanonicalProfile_rotation_identity positive negative positive
    (length := 1) (by norm_num) differencePositive positiveNonzero
  simpa only [rotationSelf, Complex.ofReal_one, one_mul, inv_one, one_pow, div_one] using identity.symm

theorem exists_halfDiagonal_configuration_matching
    (referencePositive referenceNegative : ℂ)
    (referenceDifference : 0 < ‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2)
    {accuracy : ℝ} (accuracyPositive : 0 < accuracy) :
    ∃ tolerance > (0 : ℝ), ∀ positive negative asymmetry : ℂ, ∀ length : ℝ, 0 < length →
      0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2 →
      |(‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2 -
        (‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2)| < tolerance →
      ‖halfDiagonalShape positive negative - halfDiagonalShape referencePositive referenceNegative‖ < tolerance →
      ‖asymmetry‖ / length < tolerance →
      ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
        ‖(fun patch => ((length : ℂ) * rotation)⁻¹ * quadrupoleCentroidOffset positive negative asymmetry patch) -
          centrallySymmetricFourPoint referencePositive referenceNegative‖ < accuracy := by
  have referenceNorm : 0 < ‖referencePositive‖ := by
    nlinarith [sq_nonneg ‖referenceNegative‖, norm_nonneg referencePositive]
  have referenceNonzero : referencePositive ≠ 0 := norm_pos_iff.mp referenceNorm
  have ratioIdentity := halfDiagonalRatioFromShape_reconstruct referencePositive referenceNegative referenceNonzero
  change halfDiagonalRatioFromShape (halfDiagonalShape referencePositive referenceNegative) =
    referenceNegative / referencePositive at ratioIdentity
  have continuous := halfDiagonalCanonicalProfile_continuousAt
    (difference := ‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2)
    (shape := halfDiagonalShape referencePositive referenceNegative)
    (by rw [ratioIdentity]; exact halfDiagonalRatio_norm_lt_one _ _ referenceDifference)
  obtain ⟨radius, radiusPositive, closeProfile⟩ := Metric.continuousAt_iff.mp continuous (accuracy / 2) (by positivity)
  let tolerance := min radius (accuracy / 2)
  refine ⟨tolerance, lt_min radiusPositive (by positivity), ?_⟩
  intro positive negative asymmetry length lengthPositive differencePositive differenceClose shapeClose asymmetryClose
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have positiveNonzero : positive ≠ 0 := norm_pos_iff.mp positiveNorm
  let rotation := halfDiagonalMatchingRotation positive referencePositive
  have rotationNorm : ‖rotation‖ = 1 := halfDiagonalMatchingRotation_norm positiveNonzero referenceNonzero
  refine ⟨rotation, rotationNorm, ?_⟩
  have profileClose := closeProfile (show dist
      (((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2), halfDiagonalShape positive negative)
      ((‖referencePositive‖ ^ 2 - ‖referenceNegative‖ ^ 2), halfDiagonalShape referencePositive referenceNegative) < radius by
    rw [Prod.dist_eq, max_lt_iff, Real.dist_eq, dist_eq_norm]
    exact ⟨differenceClose.trans_le (min_le_left _ _), shapeClose.trans_le (min_le_left _ _)⟩)
  rw [dist_eq_norm] at profileClose
  have phaseNorm : ‖referencePositive / (‖referencePositive‖ : ℂ)‖ = 1 := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self referenceNorm.ne']
  have centralClose : ‖(fun patch => ((length : ℂ) * rotation)⁻¹ * centrallySymmetricFourPoint positive negative patch) -
      centrallySymmetricFourPoint referencePositive referenceNegative‖ < accuracy / 2 := by
    rw [halfDiagonalCanonicalProfile_rotation_identity positive negative referencePositive lengthPositive differencePositive referenceNonzero,
      ← halfDiagonalCanonicalProfile_reference referencePositive referenceNegative referenceDifference, ← smul_sub, norm_smul, phaseNorm, one_mul]
    exact profileClose
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (fun patch => ((length : ℂ) * rotation)⁻¹ * quadrupoleCentroidOffset positive negative asymmetry patch)
    (fun patch => ((length : ℂ) * rotation)⁻¹ * centrallySymmetricFourPoint positive negative patch)
    (centrallySymmetricFourPoint referencePositive referenceNegative)
  have first := normalized_quadrupoleCentroidOffset_error positive negative asymmetry lengthPositive rotationNorm
  have small := asymmetryClose.trans_le (min_le_right _ _)
  linarith

end EulerNonuniqueness.Section6
