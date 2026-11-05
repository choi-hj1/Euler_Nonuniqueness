import EulerNonuniqueness.Section6.PaperPairedComplexMoment
import EulerNonuniqueness.Section6.PhysicalMomentTargetCoefficient

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_paired_literal_moment_strain_error
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
        (scales.circulation (index.val + 1) * ‖firstSeparation + secondSeparation‖ /
            (Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 3) +
          3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
              (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
            512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
            (2 * Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) +
          352 * scales.circulation (index.val + 1) * ‖firstCenter - secondCenter‖ ^ 2 * length /
            (Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 5)) := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have circulationNonzero : (scales.circulation (index.val + 1) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr circulationPositive.ne'
  have estimate := evolution.quadrupole_paired_strain_moment_error inside amplitudePositive frequencyPositive ratioPositive
    index location firstCenter secondCenter firstSeparation secondSeparation
    (targetMoment / (scales.circulation (index.val + 1) : ℂ)) positionsEquation control nonnegative small gapPositive
    radiusSmall sourceSeparated lengthPositive firstBound secondBound pairSeparated far
  dsimp only at estimate
  have targetIdentity :
      -3 * Complex.I * ((scales.circulation (index.val + 1) / (2 * Real.pi) : ℝ) : ℂ) *
        star (targetMoment / (scales.circulation (index.val + 1) : ℂ)) /
          star (location - (firstCenter + secondCenter) / 2) ^ 4 =
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
        (3 * targetMoment / (location - (firstCenter + secondCenter) / 2) ^ 4) := by
    exact Section6.physicalMomentTarget_strain_identity circulationPositive.ne' targetMoment
      (location - (firstCenter + secondCenter) / 2)
  rw [targetIdentity, abs_of_pos (div_pos circulationPositive (by positivity : 0 < 2 * Real.pi))] at estimate
  have momentBound := evolution.quadrupole_paired_normalized_moment_error inside amplitudePositive frequencyPositive ratioPositive
    index firstCenter secondCenter firstSeparation secondSeparation targetMoment positionsEquation control nonnegative small
  have displacementPositive : 0 < ‖location - (firstCenter + secondCenter) / 2‖ := by
    have pairPositive : 0 < ‖firstCenter - secondCenter‖ := lt_of_lt_of_le (by positivity : 0 < 4 * length) pairSeparated
    linarith
  have multiplied := mul_le_mul_of_nonneg_left momentBound
    (show 0 ≤ 3 / (2 * Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) by positivity)
  apply estimate.trans
  have momentTerm :
      3 * (scales.circulation (index.val + 1) / (2 * Real.pi)) *
          ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) -
            targetMoment / (scales.circulation (index.val + 1) : ℂ)‖ /
          ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 ≤
      3 * (‖(∫ position, quadrupoleDensity scales motion time index position •
          (position - quadrupoleCenter motion time index) ^ 2) - targetMoment‖ +
        512 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation) /
        (2 * Real.pi * ‖location - (firstCenter + secondCenter) / 2‖ ^ 4) := by
    convert multiplied using 1 <;> ring
  convert add_le_add_left (add_le_add_right (add_le_add_left momentTerm
    (2 * (scales.circulation (index.val + 1) / (2 * Real.pi)) * ‖firstSeparation + secondSeparation‖ /
      ‖location - (firstCenter + secondCenter) / 2‖ ^ 3))
    (704 * (scales.circulation (index.val + 1) / (2 * Real.pi)) * ‖firstCenter - secondCenter‖ ^ 2 * length /
      ‖location - (firstCenter + secondCenter) / 2‖ ^ 5))
    (4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation / (Real.pi * gap ^ 4)) using 1 <;> ring

end EulerNonuniqueness.Paper
