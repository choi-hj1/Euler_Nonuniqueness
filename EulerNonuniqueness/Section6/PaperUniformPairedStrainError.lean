import EulerNonuniqueness.Section6.PaperPairedNeutralStrain

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_uniform_paired_strain_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap length observationDistance pairRadius : ℝ}
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
    (far : ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2)
    (observationPositive : 0 < observationDistance)
    (observationLower : observationDistance ≤ ‖location - (firstCenter + secondCenter) / 2‖)
    (pairUpper : ‖firstCenter - secondCenter‖ ≤ pairRadius) :
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
          (3 * targetMoment / (location - (firstCenter + secondCenter) / 2) ^ 4))‖ ≤
      4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 4) +
        (4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
            (Real.pi * observationDistance ^ 3) +
          3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
              (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
            512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
            (2 * Real.pi * observationDistance ^ 4) +
          352 * scales.circulation (index.val + 1) * pairRadius ^ 2 * length /
            (Real.pi * observationDistance ^ 5)) := by
  have estimate := evolution.quadrupole_paired_neutral_moment_strain_error inside amplitudePositive
    frequencyPositive ratioPositive index location firstCenter secondCenter firstSeparation secondSeparation targetMoment
    positionsEquation control nonnegative small gapPositive radiusSmall sourceSeparated lengthPositive firstBound secondBound
    pairSeparated far
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  have neutralBound : 4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
      (Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) ≤
      4 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ /
      (Real.pi * observationDistance ^ 3) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ observationPositive.le observationLower 3) Real.pi_pos.le)
  have momentBound : 3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
      (2 * Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) ≤
      3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
      (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
      512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
      (2 * Real.pi * observationDistance ^ 4) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ observationPositive.le observationLower 4) (by positivity))
  have numeratorBound : 352 * scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ ^ 2 * length ≤
      352 * scales.circulation (index.val + 1) * pairRadius ^ 2 * length :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) pairUpper 2) (by positivity)) lengthPositive.le
  have tailBound := div_le_div₀ (by positivity : 0 ≤ 352 * scales.circulation (index.val + 1) * pairRadius ^ 2 * length)
    numeratorBound (by positivity : 0 < Real.pi * observationDistance ^ 5)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ observationPositive.le observationLower 5) Real.pi_pos.le)
  exact estimate.trans (add_le_add_left (add_le_add (add_le_add neutralBound momentBound) tailBound) _)

end EulerNonuniqueness.Paper

