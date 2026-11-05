import EulerNonuniqueness.Section5.CascadeCompatibleStablePointRemainder
import EulerNonuniqueness.Section5.CascadeGivenMapCanonicalStrainForcing
import EulerNonuniqueness.Section5.CascadeSaddleLeadingStrainEquation

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_compatible_stable_strain_remainder
    {graph coordinate : ℝ → ℝ}
    (graphAnalytic : AnalyticAt ℝ graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (certificateOrbit : SeparatingOrbit) (certificateNormalized : IsNormalizedSeparatingOrbit certificateOrbit)
    (certificateCompatible : ∀ᶠ time : ℝ in atBot,
      orbitStableShape certificateOrbit time = graph (orbitUnstableShape certificateOrbit time)) :
    ∃ chartConstant ≥ (1 : ℝ), ∃ pointConstant ≥ (1 : ℝ),
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rawCap > (0 : ℝ),
    ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (1 : ℝ),
    ∀ tolerance : ℝ, 0 < tolerance →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ {scaleRoot boundaryConstant threshold referenceConstant : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ thresholdMax → 0 ≤ referenceConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ current ∈ Icc 0 finish, |unstableShape prepared.trajectory.movingFamily.patchMotion current index| +
      |stableShape prepared.trajectory.movingFamily.patchMotion current index| ≤ radius) →
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let length := changed.length (index.val + 1)
    let omega := changed.omega (index.val + 1)
    let macroRadius := factor / 39321600 * changed.location (index.val + 1)
    let ownRadius := factor / 39321600 * length
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let leading := quadrupoleRelativeLeadingStrain changed first second time index
    let relative := referenceStraightenedShape first graph coordinate index time -
      referenceStraightenedShape second graph coordinate index time
    let shape := |relative.1| + |relative.2|
    let dilation := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
    let referenceSize := chartConstant * referenceConstant *
      ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let blockTerms := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
      quadrupoleExteriorCoefficient changed second index time macroRadius power‖
    let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first current index patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
            ownRadius (power + 1) time‖
    Summable blockTerms ∧ (∀ patch : Fin 4, Summable (patchTerms patch)) ∧
    |(relativeStraightenedSaddleStrainRemainder changed
        (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate index time).2| ≤
      pointConstant * |omega| *
        ((shape + dilation + referenceSize) * |relative.2| + referenceSize * (shape + dilation)) +
      (tolerance * (‖relativeNormalizedFirstMoment changed first second index time‖ + prepared.rawSourceCenteredState time index + shape) +
      constant * omega * epsilon * (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power +
      constant * (length / macroRadius) * (changed.strain * prepared.rawSourceCenteredState time index + ∑' power : ℕ, blockTerms power) +
      constant * referenceSize * ‖leading‖) := by
  have graphSmooth : ContDiffAt ℝ 2 graph 0 := graphAnalytic.contDiffAt
  obtain ⟨chartConstant, chartOne, pointConstant, pointOne, thresholdMax, thresholdPositive,
    thresholdEighth, pointRadius, pointPositive, pointQuarter, points⟩ :=
    exists_uniform_actual_compatible_stable_point_remainder graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
      certificateOrbit certificateNormalized certificateCompatible
  obtain ⟨canonicalRadius, canonicalPositive, canonicalQuarter, rawCap, capPositive, canonicals⟩ :=
    exists_uniform_actual_given_map_canonical_strain_forcing graphSmooth coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  let radius := min pointRadius canonicalRadius
  have radiusPositive : 0 < radius := lt_min pointPositive canonicalPositive
  have radiusPoint : radius ≤ pointRadius := min_le_left _ _
  have radiusCanonical : radius ≤ canonicalRadius := min_le_right _ _
  refine ⟨chartConstant, chartOne, pointConstant, pointOne, thresholdMax, thresholdPositive,
    thresholdEighth, radius, radiusPositive, radiusPoint.trans pointQuarter, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantOne, canonicalFactory⟩ := canonicals factorPositive factorSmall
  refine ⟨constant, constantOne, ?_⟩
  intro tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive orbit sectionTime
    scaleRoot boundaryConstant threshold referenceConstant rootOne boundaryOne thresholdBound referenceNonnegative
  have rootPositive : 0 < scaleRoot := zero_lt_one.trans_le rootOne
  have boundaryNonnegative : 0 ≤ boundaryConstant := zero_le_one.trans boundaryOne
  have factorEighth : factor ≤ 1 / 8 := factorSmall.trans (by norm_num)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [points scales amplitudePositive ratioBound alphaPositive rootPositive boundaryNonnegative
      factorPositive factorEighth thresholdBound referenceNonnegative,
    canonicalFactory chartConstant chartOne tolerance tolerancePositive scales amplitudePositive ratioBound alphaPositive
      orbit sectionTime rootOne boundaryOne thresholdSmall referenceNonnegative]
    with frequency pointEstimate canonicalEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative
    finishBound small time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let motions := cascadePairedMotion prepared.toCascadeMaterialPreparedPair
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let macroRadius := factor / 39321600 * changed.location (index.val + 1)
  let ownRadius := factor / 39321600 * length
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let leading := quadrupoleRelativeLeadingStrain changed first second time index
  let relative := referenceStraightenedShape first graph coordinate index time -
    referenceStraightenedShape second graph coordinate index time
  let shape := |relative.1| + |relative.2|
  let dilation := |diagonalDifference first time index - diagonalDifference second time index| / length ^ 2
  let referenceSize := chartConstant * referenceConstant *
    ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
  let blockTerms := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed first index time macroRadius power -
    quadrupoleExteriorCoefficient changed second index time macroRadius power‖
  let patchTerms := fun (patch : Fin 4) (power : ℕ) => (96 : ℝ) ^ (power + 1) *
    ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first current index patch) ownRadius (power + 1) time -
      prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current index patch)
          ownRadius (power + 1) time‖
  let additive := tolerance *
      (‖relativeNormalizedFirstMoment changed first second index time‖ + prepared.rawSourceCenteredState time index + shape) +
    constant * omega * epsilon *
      (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
    constant * epsilon * ∑ patch : Fin 4, ∑' power : ℕ, patchTerms patch power +
    constant * (length / macroRadius) *
      (changed.strain * prepared.rawSourceCenteredState time index + ∑' power : ℕ, blockTerms power) +
    constant * referenceSize * ‖leading‖
  obtain ⟨blockSummable, patchSummable, forcingBound⟩ :=
    canonicalEstimate count phase dipoleAngle prepared path index nonterminal finish finishNonnegative finishBound
      (fun current member => (small current member).trans radiusCanonical) time inside
  change ‖referenceStraightenedForcing changed first graph coordinate index time -
    referenceStraightenedForcing changed second graph coordinate index time - leading‖ ≤ additive at forcingBound
  have pointBound := pointEstimate prepared.toCascadeMaterialPreparedPair path index nonterminal finish
    finishNonnegative finishBound (fun current member => (small current member).trans radiusPoint) time inside
  change |(relativeStraightenedSaddlePointRemainder changed motions graph coordinate index time).2| ≤
    pointConstant * |omega| *
      ((shape + dilation + referenceSize) * |relative.2| + referenceSize * (shape + dilation)) at pointBound
  have identity : relativeStraightenedSaddleStrainRemainder changed motions graph coordinate index time =
      relativeStraightenedSaddlePointRemainder changed motions graph coordinate index time +
        (referenceStraightenedForcing changed first graph coordinate index time -
          referenceStraightenedForcing changed second graph coordinate index time - leading) := rfl
  have stableForcing : |(referenceStraightenedForcing changed first graph coordinate index time -
      referenceStraightenedForcing changed second graph coordinate index time - leading).2| ≤ additive :=
    (norm_snd_le _).trans forcingBound
  refine ⟨blockSummable, patchSummable, ?_⟩
  change |(relativeStraightenedSaddleStrainRemainder changed motions graph coordinate index time).2| ≤
    pointConstant * |omega| *
      ((shape + dilation + referenceSize) * |relative.2| + referenceSize * (shape + dilation)) + additive
  rw [identity, Prod.snd_add]
  exact (abs_add_le _ _).trans (add_le_add pointBound stableForcing)

end EulerNonuniqueness.Paper
