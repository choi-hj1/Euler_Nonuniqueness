import EulerNonuniqueness.Section6.GlobalPhysicalOddInternalRelative
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory
import EulerNonuniqueness.Section6.PaperReferenceShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

theorem fourPointCentralProjection_relative_norm_le (first second : FourPointConfiguration)
    (firstCenter secondCenter : ℂ) :
    ‖centrallySymmetricFourPoint (fourPointOddPart first).1 (fourPointOddPart first).2 -
      centrallySymmetricFourPoint (fourPointOddPart second).1 (fourPointOddPart second).2‖ ≤
      ‖(fun patch => first patch - firstCenter) - (fun patch => second patch - secondCenter)‖ := by
  let difference := (fun patch => first patch - firstCenter) - (fun patch => second patch - secondCenter)
  have oddIdentity : fourPointOddPart difference = fourPointOddPart first - fourPointOddPart second := by
    change fourPointOddPart ((first - fun _ => firstCenter) - (second - fun _ => secondCenter)) = _
    rw [fourPointOddPart_sub, fourPointOddPart_sub, fourPointOddPart_sub,
      fourPointOddPart_constant, fourPointOddPart_constant, sub_zero, sub_zero]
  have oddBound := fourPointOddPart_norm_le difference
  rw [oddIdentity] at oddBound
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg difference)).mpr
  intro patch
  fin_cases patch
  · exact (norm_fst_le (fourPointOddPart first - fourPointOddPart second)).trans oddBound
  · change ‖-(fourPointOddPart first).1 - -(fourPointOddPart second).1‖ ≤ ‖difference‖
    rw [show -(fourPointOddPart first).1 - -(fourPointOddPart second).1 =
      -((fourPointOddPart first).1 - (fourPointOddPart second).1) by ring, norm_neg]
    exact (norm_fst_le (fourPointOddPart first - fourPointOddPart second)).trans oddBound
  · exact (norm_snd_le (fourPointOddPart first - fourPointOddPart second)).trans oddBound
  · change ‖-(fourPointOddPart first).2 - -(fourPointOddPart second).2‖ ≤ ‖difference‖
    rw [show -(fourPointOddPart first).2 - -(fourPointOddPart second).2 =
      -((fourPointOddPart first).2 - (fourPointOddPart second).2) by ring, norm_neg]
    exact (norm_snd_le (fourPointOddPart first - fourPointOddPart second)).trans oddBound

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_paper_odd_internal_relative_bound :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ {count : ℕ} (scales : Scales)
      (first second : PatchMotion count) (index : Fin count) (time : ℝ),
      0 < scales.frequency → 0 < scales.ratio →
      (positiveHalfDiagonal second time index) ≠ 0 →
      ‖positiveHalfDiagonal second time index‖ / 4 ≤ ‖positiveHalfDiagonal first time index‖ →
      (1 / 32 : ℝ) ≤ ‖negativeHalfDiagonal first time index‖ / ‖positiveHalfDiagonal first time index‖ →
      ‖negativeHalfDiagonal first time index‖ / ‖positiveHalfDiagonal first time index‖ ≤ 3 / 4 →
      (1 / 32 : ℝ) ≤ ‖negativeHalfDiagonal second time index‖ / ‖positiveHalfDiagonal second time index‖ →
      ‖negativeHalfDiagonal second time index‖ / ‖positiveHalfDiagonal second time index‖ ≤ 3 / 4 →
      4 * (‖centroidAsymmetry first time index‖ + ‖centroidAsymmetry second time index‖) <
        radius * ‖positiveHalfDiagonal second time index‖ →
      ‖fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid first time index patch) -
        fourPointOddInternalError (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
          (fun patch => patchCentroid second time index patch)‖ / scales.length (index.val + 1) ≤
      bound * scales.omega (index.val + 1) * scales.length (index.val + 1) /
        ‖positiveHalfDiagonal second time index‖ ^ 3 *
          ((‖centroidAsymmetry first time index‖ + ‖centroidAsymmetry second time index‖) *
              ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ +
            (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
              (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ /
                ‖positiveHalfDiagonal second time index‖) * ‖centroidAsymmetry second time index‖ ^ 2) := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointOddInternalError_global_physical_relative_bound
      (by norm_num : (0 : ℝ) < 1 / 32) (by norm_num : (1 / 32 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 4)
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro count scales first second index time frequencyPositive ratioPositive positiveNonzero positiveComparison
    firstLower firstUpper secondLower secondUpper small
  let firstPositions : FourPointConfiguration := fun patch => patchCentroid first time index patch
  let secondPositions : FourPointConfiguration := fun patch => patchCentroid second time index patch
  have firstMoment := centroid_fourPointSignedMoment first time index
  have secondMoment := centroid_fourPointSignedMoment second time index
  change fourPointSignedMoment firstPositions = 4 * centroidAsymmetry first time index at firstMoment
  change fourPointSignedMoment secondPositions = 4 * centroidAsymmetry second time index at secondMoment
  have momentSmall : ‖fourPointSignedMoment firstPositions‖ + ‖fourPointSignedMoment secondPositions‖ <
      radius * ‖(fourPointOddPart secondPositions).1‖ := by
    rw [firstMoment, secondMoment, norm_mul, norm_mul]
    norm_num only [Complex.norm_ofNat]
    exact (by nlinarith : 4 * ‖centroidAsymmetry first time index‖ + 4 * ‖centroidAsymmetry second time index‖ <
      radius * ‖positiveHalfDiagonal second time index‖)
  have actual := estimate (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2)
    firstPositions secondPositions positiveNonzero secondLower secondUpper
    (by
      change (1 / 4 : ℝ) * ‖positiveHalfDiagonal second time index‖ ≤ ‖positiveHalfDiagonal first time index‖
      linarith) firstLower firstUpper momentSmall
  rw [firstMoment, secondMoment, ← mul_sub, norm_mul, norm_mul, norm_mul] at actual
  norm_num only [Complex.norm_ofNat] at actual
  have coefficientPositive : 0 < scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2 :=
    mul_pos (scales.omega_pos frequencyPositive ratioPositive _) (sq_pos_of_pos (scales.length_pos _))
  rw [abs_of_pos coefficientPositive] at actual
  have central := fourPointCentralProjection_relative_norm_le firstPositions secondPositions
    (quadrupoleCenter first time index) (quadrupoleCenter second time index)
  have denominatorPositive : 0 < ‖(fourPointOddPart secondPositions).1‖ := norm_pos_iff.mpr positiveNonzero
  have enlarged := actual.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right central denominatorPositive.le)
      (sq_nonneg (4 * ‖centroidAsymmetry second time index‖))) _)
    (by positivity : 0 ≤ bound * (scales.omega (index.val + 1) * scales.length (index.val + 1) ^ 2) /
      (16 * ‖(fourPointOddPart secondPositions).1‖ ^ 3)))
  apply (div_le_div_of_nonneg_right enlarged (scales.length_pos _).le).trans_eq
  change _ = bound * scales.omega (index.val + 1) * scales.length (index.val + 1) /
    ‖(fourPointOddPart secondPositions).1‖ ^ 3 *
      ((‖centroidAsymmetry first time index‖ + ‖centroidAsymmetry second time index‖) *
        ‖centroidAsymmetry first time index - centroidAsymmetry second time index‖ +
        (‖(fun patch => firstPositions patch - quadrupoleCenter first time index) -
          (fun patch => secondPositions patch - quadrupoleCenter second time index)‖ /
          ‖(fourPointOddPart secondPositions).1‖) * ‖centroidAsymmetry second time index‖ ^ 2)
  field_simp [(scales.length_pos (index.val + 1)).ne']
  <;> ring

end EulerNonuniqueness.Paper
