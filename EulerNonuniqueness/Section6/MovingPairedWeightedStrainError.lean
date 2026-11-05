import EulerNonuniqueness.Section6.PaperUniformPairedStrainError
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.Section6.LaplaceSourceErrorBound

noncomputable section

open Set MeasureTheory

private theorem measurable_shifted_strain {source : ℝ → EulerNonuniqueness.Vorticity}
    (sourceMeasurable : Measurable (Function.uncurry source)) {location : ℝ → ℂ}
    (locationMeasurable : Measurable location) (start : ℝ) :
    Measurable (fun elapsed => EulerNonuniqueness.Section6.vorticityComplexStrain
      (source (start + elapsed)) (location elapsed)) := by
  have shiftedSource : Measurable (Function.uncurry (fun elapsed => source (start + elapsed))) :=
    sourceMeasurable.comp ((measurable_const.add measurable_fst).prodMk measurable_snd)
  exact EulerNonuniqueness.Section6.measurable_vorticityComplexStrain_along shiftedSource locationMeasurable

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000

theorem quadrupole_literal_weighted_strain_error {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {finalTime start horizon deformation gap length observationDistance pairRadius decay : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion finalTime)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (index : Fin count)
    (location firstCenter secondCenter firstSeparation secondSeparation targetMoment : ℝ → ℂ)
    (locationContinuous : Continuous location) (firstContinuous : Continuous firstCenter)
    (secondContinuous : Continuous secondCenter) (targetContinuous : Continuous targetMoment)
    (horizonNonnegative : 0 ≤ horizon) (decayPositive : 0 < decay)
    (timesInside : ∀ elapsed ∈ Icc 0 horizon, start + elapsed ∈ Icc 0 finalTime)
    (positionsEquation : ∀ elapsed ∈ Icc 0 horizon,
      Section6.relabelNegativePoints (fun patch => patchCentroid family.patchMotion (start + elapsed) index patch) =
        Section6.twoDipoleConfiguration (firstCenter elapsed) (secondCenter elapsed)
          (firstSeparation elapsed) (secondSeparation elapsed))
    (control : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      BoundaryCloseToCircle scales family.patchMotion (start + elapsed) index patch deformation)
    (nonnegative : 0 ≤ deformation) (small : deformation ≤ 1 / 16)
    (gapPositive : 0 < gap) (radiusSmall : 4 * scales.radius (index.val + 1) ≤ gap)
    (sourceSeparated : ∀ elapsed ∈ Icc 0 horizon, ∀ patch,
      gap ≤ ‖location elapsed - patchCentroid family.patchMotion (start + elapsed) index patch‖)
    (lengthPositive : 0 < length)
    (firstBound : ∀ elapsed ∈ Icc 0 horizon, ‖firstSeparation elapsed‖ ≤ 2 * length)
    (secondBound : ∀ elapsed ∈ Icc 0 horizon, ‖secondSeparation elapsed‖ ≤ 2 * length)
    (pairSeparated : ∀ elapsed ∈ Icc 0 horizon, 4 * length ≤ ‖firstCenter elapsed - secondCenter elapsed‖)
    (far : ∀ elapsed ∈ Icc 0 horizon,
      ‖firstCenter elapsed - secondCenter elapsed‖ ≤
        ‖location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2‖ / 2)
    (observationPositive : 0 < observationDistance)
    (observationLower : ∀ elapsed ∈ Icc 0 horizon,
      observationDistance ≤ ‖location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2‖)
    (pairUpper : ∀ elapsed ∈ Icc 0 horizon, ‖firstCenter elapsed - secondCenter elapsed‖ ≤ pairRadius) :
    let error := fun elapsed => Section6.vorticityComplexStrain
      (quadrupoleDensity scales family.patchMotion (start + elapsed) index) (location elapsed) -
        (-(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
          (3 * targetMoment elapsed / (location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2) ^ 4))
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * ‖error elapsed‖) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖error elapsed‖) ≤
        (4096 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
            (Real.pi * gap ^ 4) +
          768 * scales.circulation (index.val + 1) * scales.radius (index.val + 1) ^ 2 * deformation /
            (Real.pi * observationDistance ^ 4) +
          352 * scales.circulation (index.val + 1) * pairRadius ^ 2 * length /
            (Real.pi * observationDistance ^ 5)) / decay +
        (4 * scales.circulation (index.val + 1) / (Real.pi * observationDistance ^ 3)) *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
            ‖centroidAsymmetry family.patchMotion (start + elapsed) index‖) +
        (3 / (2 * Real.pi * observationDistance ^ 4)) *
          (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
            ‖(∫ position, quadrupoleDensity scales family.patchMotion (start + elapsed) index position •
              (position - quadrupoleCenter family.patchMotion (start + elapsed) index) ^ 2) - targetMoment elapsed‖) := by
  dsimp only
  have shiftContinuous : Continuous (fun elapsed : ℝ => start + elapsed) := continuous_const.add continuous_id
  have sourceMeasurable := family.measurable_quadrupoleDensity scales densityEquation index
  have strainMeasurable := measurable_shifted_strain
    (source := fun time => quadrupoleDensity scales family.patchMotion time index)
    sourceMeasurable locationContinuous.measurable start
  have modelMeasurable : Measurable (fun elapsed =>
      -(Complex.I / ((2 * Real.pi : ℝ) : ℂ)) * star
        (3 * targetMoment elapsed / (location elapsed - (firstCenter elapsed + secondCenter elapsed) / 2) ^ 4)) := by
    fun_prop
  have neutralContinuous : Continuous (fun elapsed => centroidAsymmetry family.patchMotion (start + elapsed) index) := by
    unfold centroidAsymmetry
    exact (((((family.patchCentroid_continuous index 0).add
      (family.patchCentroid_continuous index 1)).sub
      (family.patchCentroid_continuous index 2)).sub
      (family.patchCentroid_continuous index 3)).div_const 4).comp shiftContinuous
  have momentContinuous := ((family.quadrupole_complex_moment_continuous scales index).comp shiftContinuous).sub targetContinuous
  have circulationNonnegative := (scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)).le
  apply Section6.laplace_source_error_bound (strainMeasurable.sub modelMeasurable)
    neutralContinuous momentContinuous decayPositive (by positivity) (by positivity) (by positivity) horizonNonnegative
  intro elapsed member
  have estimate := evolution.quadrupole_uniform_paired_strain_error (timesInside elapsed member)
    amplitudePositive frequencyPositive ratioPositive index (location elapsed) (firstCenter elapsed)
    (secondCenter elapsed) (firstSeparation elapsed) (secondSeparation elapsed) (targetMoment elapsed)
    (positionsEquation elapsed member) (control elapsed member) nonnegative small gapPositive radiusSmall
    (sourceSeparated elapsed member) lengthPositive (firstBound elapsed member) (secondBound elapsed member)
    (pairSeparated elapsed member) (far elapsed member) observationPositive (observationLower elapsed member)
    (pairUpper elapsed member)
  convert estimate using 1
  simp only [Function.comp_apply]
  ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
