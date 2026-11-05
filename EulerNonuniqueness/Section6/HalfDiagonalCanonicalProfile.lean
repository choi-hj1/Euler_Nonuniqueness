import EulerNonuniqueness.Section6.HalfDiagonalPolarReconstruction
import EulerNonuniqueness.Section6.FourPointCenterProjection

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

def halfDiagonalShape (positive negative : ℂ) : ℝ × ℝ :=
  (((‖negative‖ ^ 2 / ‖positive‖ ^ 2 - rhombusRatio) / rhombusRatio +
      (2 * Complex.arg (negative / positive) - Real.pi) / Real.sqrt 2) / 2,
    ((‖negative‖ ^ 2 / ‖positive‖ ^ 2 - rhombusRatio) / rhombusRatio -
      (2 * Complex.arg (negative / positive) - Real.pi) / Real.sqrt 2) / 2)

def halfDiagonalCanonicalProfile (difference : ℝ) (shape : ℝ × ℝ) : FourPointConfiguration :=
  centrallySymmetricFourPoint
    (Real.sqrt (difference / (1 - ‖halfDiagonalRatioFromShape shape‖ ^ 2)) : ℂ)
    ((Real.sqrt (difference / (1 - ‖halfDiagonalRatioFromShape shape‖ ^ 2)) : ℂ) * halfDiagonalRatioFromShape shape)

theorem halfDiagonalCanonicalProfile_continuousAt {difference : ℝ} {shape : ℝ × ℝ}
    (ratioSmall : ‖halfDiagonalRatioFromShape shape‖ < 1) :
    ContinuousAt (fun data : ℝ × (ℝ × ℝ) => halfDiagonalCanonicalProfile data.1 data.2) (difference, shape) := by
  have denominatorNonzero : 1 - ‖halfDiagonalRatioFromShape shape‖ ^ 2 ≠ 0 := by
    nlinarith [norm_nonneg (halfDiagonalRatioFromShape shape)]
  have ratioContinuous : ContinuousAt (fun data : ℝ × (ℝ × ℝ) => halfDiagonalRatioFromShape data.2)
      (difference, shape) := halfDiagonalRatioFromShape_continuous.continuousAt.comp continuousAt_snd
  have denominatorContinuous : ContinuousAt (fun data : ℝ × (ℝ × ℝ) =>
      1 - ‖halfDiagonalRatioFromShape data.2‖ ^ 2) (difference, shape) :=
    continuousAt_const.sub (ratioContinuous.norm.pow 2)
  have amplitudeContinuous : ContinuousAt (fun data : ℝ × (ℝ × ℝ) =>
      Real.sqrt (data.1 / (1 - ‖halfDiagonalRatioFromShape data.2‖ ^ 2))) (difference, shape) :=
    (continuousAt_fst.div denominatorContinuous denominatorNonzero).sqrt
  apply continuousAt_pi.mpr
  intro patch
  have complexAmplitude := Complex.continuous_ofReal.continuousAt.comp amplitudeContinuous
  fin_cases patch
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude.neg
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using complexAmplitude.mul ratioContinuous
  · simpa [halfDiagonalCanonicalProfile, centrallySymmetricFourPoint] using (complexAmplitude.mul ratioContinuous).neg

def halfDiagonalMatchingRotation (positive referencePositive : ℂ) : ℂ :=
  (positive / (‖positive‖ : ℂ)) / (referencePositive / (‖referencePositive‖ : ℂ))

theorem halfDiagonalMatchingRotation_norm {positive referencePositive : ℂ}
    (positiveNonzero : positive ≠ 0) (referenceNonzero : referencePositive ≠ 0) :
    ‖halfDiagonalMatchingRotation positive referencePositive‖ = 1 := by
  unfold halfDiagonalMatchingRotation
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm,
    div_self (norm_ne_zero_iff.mpr positiveNonzero), div_self (norm_ne_zero_iff.mpr referenceNonzero), div_one]

theorem halfDiagonalCanonicalProfile_rotation_identity (positive negative referencePositive : ℂ)
    {length : ℝ} (lengthPositive : 0 < length)
    (differencePositive : 0 < ‖positive‖ ^ 2 - ‖negative‖ ^ 2)
    (referenceNonzero : referencePositive ≠ 0) :
    (fun patch => ((length : ℂ) * halfDiagonalMatchingRotation positive referencePositive)⁻¹ *
      centrallySymmetricFourPoint positive negative patch) =
    (referencePositive / (‖referencePositive‖ : ℂ)) •
      halfDiagonalCanonicalProfile ((‖positive‖ ^ 2 - ‖negative‖ ^ 2) / length ^ 2)
        (halfDiagonalShape positive negative) := by
  have positiveNorm : 0 < ‖positive‖ := by nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have positiveNonzero : positive ≠ 0 := norm_pos_iff.mp positiveNorm
  have reconstruct := halfDiagonalRatioFromShape_reconstruct positive negative positiveNonzero
  change halfDiagonalRatioFromShape (halfDiagonalShape positive negative) = negative / positive at reconstruct
  unfold halfDiagonalCanonicalProfile
  rw [reconstruct, halfDiagonalAmplitude_reconstruct positive negative lengthPositive differencePositive]
  funext patch
  fin_cases patch <;> simp only [centrallySymmetricFourPoint, Pi.smul_apply, smul_eq_mul]
  all_goals
    unfold halfDiagonalMatchingRotation
    simp only [Complex.ofReal_div]
    field_simp [positiveNonzero, referenceNonzero, Complex.ofReal_ne_zero.mpr positiveNorm.ne',
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr referenceNonzero), Complex.ofReal_ne_zero.mpr lengthPositive.ne']
    <;> ring

end EulerNonuniqueness.Section6
