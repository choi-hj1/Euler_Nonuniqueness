import EulerNonuniqueness.Section5.UniversalShapeDepartureStop
import EulerNonuniqueness.Section6.NormalizedOrbitDepartureTarget

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_universal_material_stop_one_of_normalForm_departures
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape orbit time = graph (orbitUnstableShape orbit time))
    (sectionTime : ℝ) {factor error : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1 / 8)
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
    ∀ᶠ incomingTime : ℝ in atBot,
    0 < coordinate (orbitUnstableShape orbit incomingTime) ∧
    ∃ radius > (0 : ℝ), ∃ tolerance > (0 : ℝ),
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
        |unstableShape prepared.trajectory.movingFamily.patchMotion start index| +
          |stableShape prepared.trajectory.movingFamily.patchMotion start index| < radius ∧
        |coordinate (unstableShape prepared.trajectory.movingFamily.patchMotion start index) -
            coordinate (orbitUnstableShape orbit incomingTime)| +
          |stableShape prepared.trajectory.movingFamily.patchMotion start index -
            graph (unstableShape prepared.trajectory.movingFamily.patchMotion start index)| < tolerance) →
    path.stop = 1 := by
  obtain ⟨radius, radiusPositive, constant, constantOne, entry⟩ :=
    normalizedSeparatingOrbit_normalForm_entry_control graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative orbit normalized compatible
  filter_upwards [entry, normalizedSeparatingOrbit_eventually_positive_coordinate coordinateZero
    coordinateDerivative orbit normalized, eventually_lt_atBot sectionTime] with incomingTime entry positive timeOrder
  refine ⟨positive, radius, radiusPositive, ?_⟩
  obtain ⟨shapeTolerance, shapePositive, stopFactory⟩ :=
    exists_universal_material_stop_one_of_shape_departures orbit normalized sectionTime incomingTime timeOrder
      factorPositive factorSmall errorPositive errorSmall referenceSeparated distanceLarge separationClose referenceOutgoing
  refine ⟨shapeTolerance / constant, div_pos shapePositive (by linarith), ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive threshold scaleRoot boundaryConstant rootPositive boundaryNonnegative
  filter_upwards [stopFactory scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative]
    with frequency stops
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path thresholdSmall departures
  apply stops count phase dipoleAngle prepared path thresholdSmall
  intro index nonterminal
  rcases departures index nonterminal with radial | ⟨start, startInside, radial, pointSmall, close⟩
  · exact Or.inl radial
  · right
    refine ⟨start, startInside, radial, ?_⟩
    have bound := entry (unstableShape prepared.trajectory.movingFamily.patchMotion start index,
      stableShape prepared.trajectory.movingFamily.patchMotion start index) pointSmall
    apply bound.trans_lt
    have strict := mul_lt_mul_of_pos_left close (by linarith : 0 < constant)
    simpa only [mul_div_cancel₀ shapeTolerance (ne_of_gt (by linarith : 0 < constant))] using strict

end EulerNonuniqueness.Paper
