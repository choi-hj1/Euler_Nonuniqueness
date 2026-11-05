import EulerNonuniqueness.Section5.UniversalMatchedPassageContinuation
import EulerNonuniqueness.Section5.CascadePrehitInternalGap
import EulerNonuniqueness.Section5.CascadeTerminalSectionContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_universal_material_stop_one_of_incoming_matches
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (sectionTime incomingTime : ℝ) (timeOrder : incomingTime < sectionTime)
    {factor error : ℝ} (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
    (errorPositive : 0 < error) (errorSmall : error ≤ 1 / 64)
    (referenceSeparated : ∀ time : ℝ, ∀ target source : Fin 4, source ≠ target →
      2 * factor ≤ ‖centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) target -
        centrallySymmetricFourPoint (orbit.positive time) (orbit.negative time) source‖)
    (distanceLarge : 512 ≤ separationRadius orbit sectionTime)
    (separationClose : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ error / 2)
    (referenceOutgoing : (7 / 8 : ℝ) * separationRadius orbit sectionTime ≤
      (Complex.I * star (Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))) *
        (orbit.positive sectionTime - orbit.negative sectionTime)).re) :
    ∃ tolerance > (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ {threshold scaleRoot boundaryConstant : ℝ}, 0 < scaleRoot → 0 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, threshold ≤ 1 / 2 →
    (∀ index : Fin count, index.val + 1 < count →
      (∀ time ∈ Icc 0 path.stop, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) ∨
      ∃ start ∈ Icc 0 path.stop, ∃ rotation : ℂ, ‖rotation‖ = 1 ∧
        ‖cascadeNormalizedPointPositions {scales with frequency := frequency} prepared.trajectory.movingFamily.patchMotion
          index start rotation 0 - centrallySymmetricFourPoint (orbit.positive incomingTime) (orbit.negative incomingTime)‖ ≤ tolerance) →
    path.stop = 1 := by
  obtain ⟨tolerance, tolerancePositive, matchedFactory⟩ :=
    exists_universal_material_matched_passage_continuation orbit normalized incomingTime sectionTime timeOrder
      factorPositive factorSmall errorPositive errorSmall referenceSeparated distanceLarge separationClose referenceOutgoing
  refine ⟨tolerance, tolerancePositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold scaleRoot boundaryConstant rootPositive boundaryNonnegative
  have matched := matchedFactory scales amplitudePositive ratioBound alphaPositive sectionTime
    (threshold := threshold) rootPositive boundaryNonnegative
  have separationCoarse : ‖orbit.positive sectionTime + orbit.negative sectionTime -
      Complex.exp (Complex.I * (orbit.limitingDipoleAngle : ℂ))‖ ≤ 1 / 128 := by linarith
  filter_upwards [matched,
    scales.eventually_material_prehit_internal_gap amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative,
    cascade_terminal_gap_continuation_of_section orbit sectionTime distanceLarge separationCoarse referenceOutgoing
      scales amplitudePositive ratioBound alphaPositive factorPositive factorSmall rootPositive boundaryNonnegative]
    with frequency matched prehit terminal
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path thresholdSmall phases
  by_contra notOne
  have premature : path.stop < 1 := lt_of_le_of_ne path.stopBound notOne
  obtain ⟨index, first, second, different, contact⟩ := path.premature_contact premature
  have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
  by_cases last : index.val + 1 = count
  · have actual := terminal count phase dipoleAngle prepared path index last path.stop
      ⟨path.stopPositive.le, le_rfl⟩ first second different
    rw [contact] at actual
    nlinarith
  have nonterminal : index.val + 1 < count := by omega
  rcases phases index nonterminal with radial | ⟨start, startInside, rotation, rotationNorm, initial⟩
  · have actual := (prehit prepared path thresholdSmall factorSmall index nonterminal path.stop
      path.stopPositive.le le_rfl radial path.stop ⟨path.stopPositive.le, le_rfl⟩).1 first second different
    rw [contact] at actual
    exact (lt_irrefl _ actual)
  · have actual := matched count phase dipoleAngle prepared path index start startInside.1 startInside.2 rotation rotationNorm
      initial path.stop ⟨startInside.2, le_rfl⟩ first second different
    rw [contact] at actual
    exact (lt_irrefl _ actual)

end EulerNonuniqueness.Paper

