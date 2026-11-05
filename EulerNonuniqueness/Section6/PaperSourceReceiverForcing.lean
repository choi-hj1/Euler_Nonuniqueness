import EulerNonuniqueness.Section6.PaperUniformPairedStrainError
import EulerNonuniqueness.Section6.ActualReceiverStrainError
import EulerNonuniqueness.Section6.SourceMomentTranslation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

theorem exists_uniform_paper_source_receiver_forcing :
    ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time deformation gap length observationDistance pairRadius : ℝ},
      ∀ (evolution : FinitePatchEvolution scales motion horizon), time ∈ Icc 0 horizon →
      0 < scales.amplitude → 0 < scales.frequency → 0 < scales.ratio → ∀ source : Fin count,
      ∀ location firstCenter secondCenter firstSeparation secondSeparation targetMoment frozenDisplacement positive negative idealPositive : ℂ,
      Section6.relabelNegativePoints (fun patch => patchCentroid motion time source patch) =
        Section6.twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation →
      (∀ patch, BoundaryCloseToCircle scales motion time source patch deformation) →
      0 ≤ deformation → deformation ≤ 1 / 16 → 0 < gap → 4 * scales.radius (source.val + 1) ≤ gap →
      (∀ patch, gap ≤ ‖location - patchCentroid motion time source patch‖) →
      0 < length → ‖firstSeparation‖ ≤ 2 * length → ‖secondSeparation‖ ≤ 2 * length →
      4 * length ≤ ‖firstCenter - secondCenter‖ →
      ‖firstCenter - secondCenter‖ ≤ ‖location - (firstCenter + secondCenter) / 2‖ / 2 →
      0 < observationDistance → observationDistance ≤ ‖location - (firstCenter + secondCenter) / 2‖ →
      ‖firstCenter - secondCenter‖ ≤ pairRadius → frozenDisplacement ≠ 0 →
      ‖(location - (firstCenter + secondCenter) / 2) - frozenDisplacement‖ ≤ ‖frozenDisplacement‖ / 2 →
      positive ≠ 0 → negative ≠ 0 → idealPositive ≠ 0 →
      |(Section6.pointShapeChart positive negative).1| + |(Section6.pointShapeChart positive negative).2| < radius →
      let actualStrain := Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) location
      let modelStrain := -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / frozenDisplacement ^ 4)
      |(Section6.pointShapeForcing positive negative (actualStrain * star positive) (actualStrain * star negative)).1 -
        (Section6.pointShapeForcing idealPositive
          (Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * idealPositive)
          (modelStrain * star idealPositive)
          (modelStrain * star (Complex.I * (Real.sqrt Section2.rhombusRatio : ℂ) * idealPositive))).1| ≤
        constant * ‖actualStrain‖ * (|(Section6.pointShapeChart positive negative).1| + |(Section6.pointShapeChart positive negative).2|) +
        4 * (4096 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * deformation /
            (Real.pi * gap ^ 4) +
          (4 * scales.circulation (source.val + 1) * ‖centroidAsymmetry motion time source‖ /
              (Real.pi * observationDistance ^ 3) +
            3 * (‖(∫ position, quadrupoleDensity scales motion time source position •
                (position - quadrupoleCenter motion time source) ^ 2) - targetMoment‖ +
              512 * scales.circulation (source.val + 1) * scales.radius (source.val + 1) ^ 2 * deformation) /
              (2 * Real.pi * observationDistance ^ 4) +
            352 * scales.circulation (source.val + 1) * pairRadius ^ 2 * length /
              (Real.pi * observationDistance ^ 5))) +
        768 * ‖targetMoment‖ * ‖(location - (firstCenter + secondCenter) / 2) - frozenDisplacement‖ /
          (Real.pi * ‖frozenDisplacement‖ ^ 5) +
        4 * ‖modelStrain‖ * ‖star positive / positive - star idealPositive / idealPositive‖ := by
  obtain ⟨constant, constantNonnegative, radius, radiusPositive, receiver⟩ := Section6.actual_receiver_strain_error
  refine ⟨constant, constantNonnegative, radius, radiusPositive, ?_⟩
  intro count scales motion horizon time deformation gap length observationDistance pairRadius evolution inside amplitudePositive frequencyPositive ratioPositive
    source location firstCenter secondCenter firstSeparation secondSeparation targetMoment frozenDisplacement positive negative idealPositive
    positionsEquation control deformationNonnegative deformationSmall gapPositive radiusSmall separated lengthPositive firstBound secondBound
    pairSeparated far observationPositive observationLower pairUpper frozenNonzero close positiveNonzero negativeNonzero idealNonzero chartSmall
  dsimp only
  have spatial := evolution.quadrupole_uniform_paired_strain_error inside amplitudePositive frequencyPositive ratioPositive
    source location firstCenter secondCenter firstSeparation secondSeparation targetMoment positionsEquation control deformationNonnegative deformationSmall
    gapPositive radiusSmall separated lengthPositive firstBound secondBound pairSeparated far observationPositive observationLower pairUpper
  have translation := Section6.physical_second_moment_strain_translation_bound targetMoment frozenNonzero close
  have total := (norm_sub_le_norm_sub_add_norm_sub
    (Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) location)
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / (location - (firstCenter + secondCenter) / 2) ^ 4))
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / frozenDisplacement ^ 4))).trans (add_le_add spatial translation)
  have actual := receiver positive negative idealPositive
    (Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) location)
    (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / frozenDisplacement ^ 4))
    positiveNonzero negativeNonzero idealNonzero chartSmall
  apply actual.trans
  have enlarged := mul_le_mul_of_nonneg_left total (by norm_num : (0 : ℝ) ≤ 4)
  have extended := add_le_add_right (add_le_add_left enlarged
    (constant * ‖Section6.vorticityComplexStrain (quadrupoleDensity scales motion time source) location‖ *
      (|(Section6.pointShapeChart positive negative).1| + |(Section6.pointShapeChart positive negative).2|)))
    (4 * ‖-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star (3 * targetMoment / frozenDisplacement ^ 4)‖ *
      ‖star positive / positive - star idealPositive / idealPositive‖)
  convert extended using 1 <;> ring

end EulerNonuniqueness.Paper
