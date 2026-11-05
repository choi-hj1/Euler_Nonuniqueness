import EulerNonuniqueness.Section6.PaperPairedMomentStrainError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem Scales.moment_increment_strain_identity (scales : Scales) (index : ℕ)
    (initialMoment direction displacement : ℂ) (elapsed : ℝ) :
    -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
      (3 * (initialMoment + scales.circulation index •
        ((-4 * Complex.I * (scales.omega index : ℂ) * (scales.length index : ℂ) ^ 2 * direction ^ 2) *
          (elapsed : ℂ))) / displacement ^ 4) =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * initialMoment / displacement ^ 4) +
        12 * (scales.omega index : ℂ) ^ 2 * (scales.length index : ℂ) ^ 4 *
          star direction ^ 2 * (elapsed : ℂ) / star displacement ^ 4 := by
  rw [mul_add, add_div, star_add, mul_add]
  congr 1
  have physical := Section6.physicalMomentRamp_strain_identity (scales.omega index)
    (scales.length index) elapsed direction displacement
  convert physical using 1
  congr 3
  rw [Complex.real_smul, Scales.circulation]
  push_cast
  ring

theorem FinitePatchEvolution.quadrupole_paired_increment_strain_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (location : ℂ)
    (firstCenter secondCenter firstSeparation secondSeparation initialMoment direction : ℂ) (elapsed : ℝ)
    (positionsEquation : Section6.relabelNegativePoints (fun patch => patchCentroid motion time index patch) =
      Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)
    (control : ∀ patch, BoundaryCloseToCircle scales motion time index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (sourceSeparated : ∀ patch, gap ≤ ‖location - patchCentroid motion time index patch‖)
    (firstBound : ‖firstSeparation‖ ≤ 2 * scales.length (index.val + 1))
    (secondBound : ‖secondSeparation‖ ≤ 2 * scales.length (index.val + 1))
    (pairSeparated : 4 * scales.length (index.val + 1) ≤ ‖firstCenter - secondCenter‖)
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2) :
    let displacement := location - (firstCenter + secondCenter) / 2
    let ramp := (-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
      (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ)
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * initialMoment / displacement ^ 4)) -
        12 * (scales.omega (index.val + 1) : ℂ) ^ 2 * (scales.length (index.val + 1) : ℂ) ^ 4 *
          star direction ^ 2 * (elapsed : ℂ) / star displacement ^ 4‖ ≤
      4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 4) +
        (scales.circulation (index.val + 1) * ‖firstSeparation + secondSeparation‖ /
            (Real.pi * ‖displacement‖ ^ 3) +
          3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
              (position - quadrupoleCenter motion time index) ^ 2) - initialMoment -
                scales.circulation (index.val + 1) • ramp‖ +
            512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
            (2 * Real.pi * ‖displacement‖ ^ 4) +
          352 * scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ ^ 2 * scales.length (index.val + 1) /
            (Real.pi * ‖displacement‖ ^ 5)) := by
  dsimp only
  have estimate := evolution.quadrupole_paired_literal_moment_strain_error inside amplitudePositive
    frequencyPositive ratioPositive index location firstCenter secondCenter firstSeparation secondSeparation
    (initialMoment + scales.circulation (index.val + 1) •
      ((-4 * Complex.I * (scales.omega (index.val + 1) : ℂ) *
        (scales.length (index.val + 1) : ℂ) ^ 2 * direction ^ 2) * (elapsed : ℂ)))
    positionsEquation control nonnegative small gapPositive radiusSmall sourceSeparated (scales.length_pos _)
    firstBound secondBound pairSeparated far
  rw [scales.moment_increment_strain_identity] at estimate
  simpa only [sub_add_eq_sub_sub] using estimate

end EulerNonuniqueness.Paper
