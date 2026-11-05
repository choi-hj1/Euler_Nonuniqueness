import EulerNonuniqueness.Section5.UniversalIncomingMatchStop
import EulerNonuniqueness.Section5.CascadeOrbitIncomingMatching
import EulerNonuniqueness.Section5.CascadePrehitMatchingAccuracy
import EulerNonuniqueness.Section5.CascadePrehitInternalGap
import EulerNonuniqueness.Section5.CascadeTerminalSectionContinuation

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_universal_material_stop_one_of_shape_departures
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
      ∃ start ∈ Icc 0 path.stop,
        (∀ time ∈ Icc 0 start, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) ∧
        |unstableShape prepared.trajectory.movingFamily.patchMotion start index - orbitUnstableShape orbit incomingTime| +
          |stableShape prepared.trajectory.movingFamily.patchMotion start index - orbitStableShape orbit incomingTime| < tolerance) →
    path.stop = 1 := by
  obtain ⟨configurationTolerance, configurationPositive, stopFactories⟩ :=
    exists_universal_material_stop_one_of_incoming_matches orbit normalized sectionTime incomingTime timeOrder
      factorPositive factorSmall errorPositive errorSmall referenceSeparated distanceLarge separationClose referenceOutgoing
  obtain ⟨shapeTolerance, shapePositive, matching⟩ :=
    normalizedSeparatingOrbit_exists_incoming_shape_matching orbit normalized incomingTime configurationPositive
  refine ⟨shapeTolerance, shapePositive, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold scaleRoot boundaryConstant rootPositive boundaryNonnegative
  have stops := stopFactories scales amplitudePositive ratioBound alphaPositive
    (threshold := threshold) rootPositive boundaryNonnegative
  filter_upwards [stops,
    scales.eventually_material_prehit_matching_accuracy amplitudePositive ratioBound alphaPositive
      (tolerance := min shapeTolerance (1 / 4)) rootPositive boundaryNonnegative
      (lt_min shapePositive (by norm_num))]
    with frequency stops accurate
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path thresholdSmall phases
  apply stops count phase dipoleAngle prepared path thresholdSmall
  intro index nonterminal
  rcases phases index nonterminal with radial | ⟨start, startInside, radial, shapeClose⟩
  · exact Or.inl radial
  · right
    have actual := accurate prepared path thresholdSmall factorSmall index nonterminal start startInside.1 startInside.2
      radial start ⟨startInside.1, le_rfl⟩
    have lengthPositive := ({scales with frequency := frequency} : Scales).length_pos (index.val + 1)
    have differencePositive : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion start index := by
      have small := actual.1.trans_le (min_le_right _ _)
      have lower := (abs_lt.mp small).1
      have quotientPositive : 0 < diagonalDifference prepared.trajectory.movingFamily.patchMotion start index /
          ({scales with frequency := frequency} : Scales).length (index.val + 1) ^ 2 := by linarith
      simpa using (lt_div_iff₀ (sq_pos_of_pos lengthPositive)).mp quotientPositive
    obtain ⟨rotation, rotationNorm, close⟩ := matching {scales with frequency := frequency}
      prepared.trajectory.movingFamily.patchMotion start index differencePositive
      (actual.1.trans_le (min_le_left _ _)) shapeClose (actual.2.trans_le (min_le_left _ _))
    exact ⟨start, startInside, rotation, rotationNorm, close.le⟩

end EulerNonuniqueness.Paper


