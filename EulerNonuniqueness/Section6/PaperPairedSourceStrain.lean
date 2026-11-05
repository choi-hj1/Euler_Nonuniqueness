import EulerNonuniqueness.Section6.PaperPatchStrainComparison

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

theorem FinitePatchEvolution.quadrupole_paired_strain_moment_error
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap length : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (inside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count) (location : ℂ)
    (firstCenter secondCenter firstSeparation secondSeparation modelMoment : ℂ)
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
    let coefficient := scales.circulation (index.val + 1) / (2 * Real.pi)
    ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time index) location -
        (-3 * Complex.I * (coefficient : ℂ) * star modelMoment /
          star (location - (firstCenter + secondCenter) / 2) ^ 4)‖ ≤
      4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
          (Real.pi * gap ^ 4) +
        (2 * |coefficient| * ‖firstSeparation + secondSeparation‖ /
            ‖location - (firstCenter + secondCenter) / 2‖ ^ 3 +
          3 * |coefficient| * ‖(firstCenter - secondCenter) * (firstSeparation - secondSeparation) - modelMoment‖ /
            ‖location - (firstCenter + secondCenter) / 2‖ ^ 4 +
          704 * |coefficient| * ‖firstCenter - secondCenter‖ ^ 2 * length /
            ‖location - (firstCenter + secondCenter) / 2‖ ^ 5) := by
  dsimp only
  have patchEstimate := evolution.quadrupole_strain_point_error inside amplitudePositive frequencyPositive ratioPositive index
    location control nonnegative small gapPositive radiusSmall sourceSeparated
  have pointIdentity : Section6.fourPointExternalPointStrain (scales.circulation (index.val + 1) / (2 * Real.pi))
      (fun patch => patchCentroid motion time index patch) location =
      Section6.fourPointExternalPointStrain (scales.circulation (index.val + 1) / (2 * Real.pi))
        (Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location := by
    rw [← Section6.fourPointExternalPointStrain_negativeLabelSwap, positionsEquation]
  rw [pointIdentity] at patchEstimate
  have pointEstimate := Section6.twoDipole_physical_strain_moment_error
    (scales.circulation (index.val + 1) / (2 * Real.pi)) lengthPositive firstBound secondBound pairSeparated far modelMoment
  exact (norm_sub_le_norm_sub_add_norm_sub _
    (Section6.fourPointExternalPointStrain (scales.circulation (index.val + 1) / (2 * Real.pi))
      (Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) location) _).trans
      (add_le_add patchEstimate pointEstimate)

end EulerNonuniqueness.Paper
