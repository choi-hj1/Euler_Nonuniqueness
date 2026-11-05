import EulerNonuniqueness.Section6.CorrectedPhaseProfile
import EulerNonuniqueness.Section6.PaperCorrectedPhaseDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem halfDiagonalCanonicalProfile_polar_reconstruction (positive negative : ℂ)
    {length phase : ℝ} (lengthPositive : 0 < length)
    (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2)
    (polar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) :
    centrallySymmetricFourPoint positive negative =
      (length : ℂ) • (Complex.exp (Complex.I * (phase : ℂ)) •
        halfDiagonalCanonicalProfile ((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2)
          (halfDiagonalShape positive negative)) := by
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have positiveNonzero : positive ≠ 0 := norm_pos_iff.mp positiveNorm
  have rotation : Complex.exp (Complex.I * (phase : ℂ)) = positive / (‖positive‖ : ℂ) := by
    apply (eq_div_iff (Complex.ofReal_ne_zero.mpr positiveNorm.ne')).mpr
    exact (mul_comm _ _).trans polar.symm
  have ratio : halfDiagonalRatioFromShape (halfDiagonalShape positive negative) = negative / positive :=
    halfDiagonalRatioFromShape_reconstruct positive negative positiveNonzero
  unfold halfDiagonalCanonicalProfile
  rw [ratio,
    halfDiagonalAmplitude_reconstruct positive negative lengthPositive differencePositive, rotation]
  funext patch
  fin_cases patch <;> simp only [centrallySymmetricFourPoint, Pi.smul_apply, smul_eq_mul, Complex.ofReal_div]
  all_goals field_simp [positiveNonzero, Complex.ofReal_ne_zero.mpr lengthPositive.ne',
    Complex.ofReal_ne_zero.mpr positiveNorm.ne'] <;> ring

theorem correctedHalfDiagonalProfile_polar_reconstruction (correction : ℝ → ℝ)
    (positive negative : ℂ) {length phase : ℝ} (lengthPositive : 0 < length)
    (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2)
    (polar : positive = (‖positive‖ : ℂ) * Complex.exp (Complex.I * (phase : ℂ))) :
    centrallySymmetricFourPoint positive negative =
      (length : ℂ) • (Complex.exp (Complex.I *
        ((phase - (Real.sqrt 2 - 1) / 4 * shapeChartAngle (halfDiagonalShape positive negative) -
          correction (halfDiagonalShape positive negative).1 : ℝ) : ℂ)) •
        correctedHalfDiagonalProfile correction
          ((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2, halfDiagonalShape positive negative)) := by
  rw [halfDiagonalCanonicalProfile_polar_reconstruction positive negative lengthPositive differencePositive polar]
  have phaseFactor : Complex.exp (Complex.I * (phase : ℂ)) =
      Complex.exp (Complex.I * ((phase - (Real.sqrt 2 - 1) / 4 * shapeChartAngle (halfDiagonalShape positive negative) -
        correction (halfDiagonalShape positive negative).1 : ℝ) : ℂ)) *
      Complex.exp (Complex.I * (((Real.sqrt 2 - 1) / 4 * shapeChartAngle (halfDiagonalShape positive negative) +
        correction (halfDiagonalShape positive negative).1 : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold correctedHalfDiagonalProfile
  rw [phaseFactor]
  simp only [smul_smul, mul_assoc]

theorem quadrupole_centroid_offset_reconstruction {count : ℕ} (motion : PatchMotion count)
    (time : ℝ) (index : Fin count) (patch : Fin 4) :
    patchCentroid motion time index patch - quadrupoleCenter motion time index =
      quadrupoleCentroidOffset (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
        (centroidAsymmetry motion time index) patch := by
  have identity (positions : Fin 4 → ℂ) (label : Fin 4) :
      positions label - (∑ current : Fin 4, positions current) / 4 =
      quadrupoleCentroidOffset ((positions 0 - positions 1) / 2) ((positions 2 - positions 3) / 2)
        ((positions 0 + positions 1 - positions 2 - positions 3) / 4) label := by
    fin_cases label
    · change positions 0 - (∑ current : Fin 4, positions current) / 4 =
        (positions 0 + positions 1 - positions 2 - positions 3) / 4 + (positions 0 - positions 1) / 2
      rw [Fin.sum_univ_four]
      ring
    · change positions 1 - (∑ current : Fin 4, positions current) / 4 =
        (positions 0 + positions 1 - positions 2 - positions 3) / 4 - (positions 0 - positions 1) / 2
      rw [Fin.sum_univ_four]
      ring
    · change positions 2 - (∑ current : Fin 4, positions current) / 4 =
        -((positions 0 + positions 1 - positions 2 - positions 3) / 4) + (positions 2 - positions 3) / 2
      rw [Fin.sum_univ_four]
      ring
    · change positions 3 - (∑ current : Fin 4, positions current) / 4 =
        -((positions 0 + positions 1 - positions 2 - positions 3) / 4) - (positions 2 - positions 3) / 2
      rw [Fin.sum_univ_four]
      ring
  exact identity (fun patch => patchCentroid motion time index patch) patch

end EulerNonuniqueness.Section6
