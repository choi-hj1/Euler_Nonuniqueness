import EulerNonuniqueness.Section6.PaperPairedMomentStrainError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem quadrupole_paired_separation_sum
    {count : ℕ} (motion : PatchMotion count) (time : ℝ) (index : Fin count)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) :
    firstSeparation + secondSeparation = (4 : ℝ) • centroidAsymmetry motion time index := by
  have positions : (fun patch => patchCentroid motion time index patch) =
      Section6.relabelNegativePoints (Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) := by
    rw [← positionsEquation, Section6.relabelNegativePoints_involutive]
  unfold centroidAsymmetry
  change firstSeparation + secondSeparation = (4 : ℝ) •
    (((fun patch => patchCentroid motion time index patch) 0 +
      (fun patch => patchCentroid motion time index patch) 1 -
      (fun patch => patchCentroid motion time index patch) 2 -
      (fun patch => patchCentroid motion time index patch) 3) / 4)
  rw [positions]
  have values : Section6.relabelNegativePoints
      (Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) =
      ![firstCenter + firstSeparation / 2, secondCenter + secondSeparation / 2,
        secondCenter - secondSeparation / 2, firstCenter - firstSeparation / 2] := by
    funext patch
    fin_cases patch <;> rfl
  rw [values]
  change firstSeparation + secondSeparation = (4 : ℝ) •
    ((firstCenter + firstSeparation / 2 + (secondCenter + secondSeparation / 2) -
      (secondCenter - secondSeparation / 2) - (firstCenter - firstSeparation / 2)) / 4)
  norm_num [Complex.real_smul]
  ring

theorem FinitePatchEvolution.quadrupole_paired_neutral_moment_strain_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap length : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (location : ℂ)
    (firstCenter secondCenter firstSeparation secondSeparation targetMoment : ℂ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (sourceSeparated : ∀ patch, gap ≤ ‖location - patchCentroid motion time index patch‖)
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (pairSeparated : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
          (3 * targetMoment / (location - (firstCenter + secondCenter) / 2) ^ 4))‖ ≤
      4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 4) +
        (4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
            (Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) +
          3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
              (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
            512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
            (2 * Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) +
          352 * scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ ^ 2 * length /
            (Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 5)) := by
  have estimate := evolution.quadrupole_paired_literal_moment_strain_error inside amplitudePositive
    frequencyPositive ratioPositive index location firstCenter secondCenter firstSeparation secondSeparation targetMoment
    positionsEquation control nonnegative small gapPositive radiusSmall sourceSeparated lengthPositive firstBound secondBound
    pairSeparated far
  rw [quadrupole_paired_separation_sum motion time index firstCenter secondCenter firstSeparation secondSeparation
    positionsEquation, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at estimate
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Paper
