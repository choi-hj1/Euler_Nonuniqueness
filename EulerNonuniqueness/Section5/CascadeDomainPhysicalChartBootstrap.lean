import EulerNonuniqueness.Section5.CascadeDomainSharpProfileBootstrap
import EulerNonuniqueness.Section5.CascadeReferenceSharpDefect
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.SourcePacketRhombusJointContinuation
import EulerNonuniqueness.Section4.RegularizedShapeBranch
import EulerNonuniqueness.General.ContinuousPrefixBootstrap

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem regularized_shape_prefix_eq_paper {count : ℕ} (motion : PatchMotion count)
    (index : Fin count) {horizon denominatorFloor : ℝ} (floorPositive : 0 < denominatorFloor)
    (positiveContinuous : ContinuousOn (fun time => positiveHalfDiagonal motion time index) (Icc 0 horizon))
    (negativeContinuous : ContinuousOn (fun time => negativeHalfDiagonal motion time index) (Icc 0 horizon))
    (denominatorLower : ∀ time ∈ Icc 0 horizon, denominatorFloor ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2)
    (initialUpper : 0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im)
    (small : ∀ time ∈ Icc 0 horizon,
      |(regularizedShapeCoordinates denominatorFloor (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).1| +
      |(regularizedShapeCoordinates denominatorFloor (1 / 16)
        (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)).2| ≤ 1 / 4) :
    ∀ time ∈ Icc 0 horizon, regularizedShapeCoordinates denominatorFloor (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index) =
        (unstableShape motion time index, stableShape motion time index) := by
  have nonzero (time : ℝ) (inside : time ∈ Icc 0 horizon) : positiveHalfDiagonal motion time index ≠ 0 := by
    intro zero
    have lower := denominatorLower time inside
    rw [zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at lower
    linarith only [lower, floorPositive]
  have quotientContinuous := negativeContinuous.div positiveContinuous nonzero
  have left (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      ((negativeHalfDiagonal motion time index / positiveHalfDiagonal motion time index) ^ 2).re < 0 :=
    regularizedShapeCoordinates_square_left (denominatorLower time inside) (small time inside)
  have upper := Section6.upperHalfPlane_of_initial_and_square_left quotientContinuous initialUpper left
  intro time inside
  exact regularizedShapeCoordinates_eq_paper_of_small_upper motion time index
    (denominatorLower time inside) (small time inside) (upper time inside)

private theorem physical_shape_strict_improvement
    {graph coordinate : ℝ → ℝ} {first second : ℝ × ℝ}
    {radius inverseRadius inverseConstant chartBudget : ℝ}
    (radiusPositive : 0 < radius) (radiusInverse : radius < inverseRadius)
    (inverseNonnegative : 0 ≤ inverseConstant)
    (inverse : ∀ left right : ℝ × ℝ, |left.1| + |left.2| < inverseRadius →
      |right.1| + |right.2| < inverseRadius →
      |left.1 - right.1| + |left.2 - right.2| ≤
        inverseConstant * ‖Section6.localNormalFormChart graph coordinate left -
          Section6.localNormalFormChart graph coordinate right‖)
    (firstSmall : |first.1| + |first.2| ≤ radius)
    (referenceSmall : |second.1| + |second.2| < radius / 8)
    (chartBound : |(Section6.localNormalFormChart graph coordinate first).1 -
        (Section6.localNormalFormChart graph coordinate second).1| +
      |(Section6.localNormalFormChart graph coordinate first).2 -
        (Section6.localNormalFormChart graph coordinate second).2| ≤ chartBudget)
    (budgetSmall : inverseConstant * chartBudget ≤ radius / 8) :
    |first.1| + |first.2| < radius / 2 := by
  have secondSmall : |second.1| + |second.2| < inverseRadius := by
    linarith only [referenceSmall, radiusInverse, radiusPositive]
  have actual := inverse first second (firstSmall.trans_lt radiusInverse) secondSmall
  have normBound : ‖Section6.localNormalFormChart graph coordinate first -
      Section6.localNormalFormChart graph coordinate second‖ ≤
      |(Section6.localNormalFormChart graph coordinate first).1 -
        (Section6.localNormalFormChart graph coordinate second).1| +
      |(Section6.localNormalFormChart graph coordinate first).2 -
        (Section6.localNormalFormChart graph coordinate second).2| := by
    rw [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  have physicalBound := actual.trans (mul_le_mul_of_nonneg_left (normBound.trans chartBound) inverseNonnegative)
  have firstAbsolute := abs_sub_abs_le_abs_sub first.1 second.1
  have secondAbsolute := abs_sub_abs_le_abs_sub first.2 second.2
  linarith only [physicalBound, firstAbsolute, secondAbsolute, referenceSmall, budgetSmall, radiusPositive]

private theorem actual_initial_regularized_geometry
    {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (index : Fin count) (nonterminal : index.val + 1 < count)
    {radius : ℝ} (radiusPositive : 0 < radius) (radiusQuarter : radius ≤ 1 / 4)
    (denominatorLower : scales.length (index.val + 1) ^ 2 / 2 ≤
      ‖positiveHalfDiagonal prepared.trajectory.movingFamily.patchMotion 0 index‖ ^ 2)
    (referenceSmall : |unstableShape prepared.reference 0 index| + |stableShape prepared.reference 0 index| < radius / 8) :
    let motion := prepared.trajectory.movingFamily.patchMotion
    let regularized := fun time => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
      (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
    Continuous (fun time => positiveHalfDiagonal motion time index) ∧
    Continuous (fun time => negativeHalfDiagonal motion time index) ∧ Continuous regularized ∧
    0 < (negativeHalfDiagonal motion 0 index / positiveHalfDiagonal motion 0 index).im ∧
    |(regularized 0).1| + |(regularized 0).2| < radius := by
  dsimp only
  let motion := prepared.trajectory.movingFamily.patchMotion
  let regularized := fun time => regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16)
    (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
  have positiveContinuous : Continuous (fun time : ℝ => positiveHalfDiagonal motion time index) := by
    exact ((prepared.trajectory.movingFamily.patchCentroid_continuous index 0).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 1)).div_const 2
  have negativeContinuous : Continuous (fun time : ℝ => negativeHalfDiagonal motion time index) := by
    exact ((prepared.trajectory.movingFamily.patchCentroid_continuous index 2).sub
      (prepared.trajectory.movingFamily.patchCentroid_continuous index 3)).div_const 2
  have diagonalContinuous : Continuous (fun time : ℝ =>
      (positiveHalfDiagonal motion time index, negativeHalfDiagonal motion time index)) :=
    positiveContinuous.prodMk negativeContinuous
  have shapeContinuous : Continuous (fun point : ℂ × ℂ =>
      regularizedShapeCoordinates (scales.length (index.val + 1) ^ 2 / 2) (1 / 16) point.1 point.2) :=
    regularizedShapeCoordinates_continuous
      (div_pos (sq_pos_of_pos (scales.length_pos _)) (by norm_num)) (by norm_num)
  have composed := shapeContinuous.comp diagonalContinuous
  have regularizedContinuous : Continuous regularized := by
    simpa only [regularized, Function.comp_def] using composed
  have positive : positiveHalfDiagonal motion 0 index = positiveHalfDiagonal prepared.reference 0 index := by
    simp only [motion, positiveHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have negative : negativeHalfDiagonal motion 0 index = negativeHalfDiagonal prepared.reference 0 index := by
    simp only [motion, negativeHalfDiagonal, prepared.nonterminal_initial_centroid index nonterminal]
  have first : unstableShape motion 0 index = unstableShape prepared.reference 0 index := by
    simp only [unstableShape, radialShape, angularShape, positive, negative]
  have second : stableShape motion 0 index = stableShape prepared.reference 0 index := by
    simp only [stableShape, radialShape, angularShape, positive, negative]
  have actualSmall : |unstableShape motion 0 index| + |stableShape motion 0 index| < radius / 8 := by
    rw [first, second]
    exact referenceSmall
  have actualQuarter : |unstableShape motion 0 index| + |stableShape motion 0 index| ≤ 1 / 4 := by
    linarith only [actualSmall, radiusPositive, radiusQuarter]
  have upper := paper_shape_ratio_im_pos_of_small motion 0 index actualQuarter
  have chartSmall : |(Section6.pointShapeChart (positiveHalfDiagonal motion 0 index) (negativeHalfDiagonal motion 0 index)).1| +
      |(Section6.pointShapeChart (positiveHalfDiagonal motion 0 index) (negativeHalfDiagonal motion 0 index)).2| ≤ 1 / 4 := by
    rw [pointShapeChart_eq_paper_shape_of_upper motion 0 index upper]
    exact actualQuarter
  have gap := Section6.pointShapeChart_reference_imaginary_gap _ _ chartSmall upper
  have agreement : regularized 0 = (unstableShape motion 0 index, stableShape motion 0 index) :=
    regularizedShapeCoordinates_eq_paper motion 0 index denominatorLower
      ((by norm_num : (1 / 16 : ℝ) ≤ 1 / 8).trans gap)
  refine ⟨positiveContinuous, negativeContinuous, regularizedContinuous, upper, ?_⟩
  change |(regularized 0).1| + |(regularized 0).2| < radius
  rw [agreement]
  linarith only [actualSmall, radiusPositive]

theorem exists_uniform_actual_domain_physical_chart_bootstrap :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ chartConstant ≥ (1 : ℝ), ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
      (∀ orbit : SeparatingOrbit, IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) ∧
      ∃ rawCap > (0 : ℝ),
      ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
      ∃ stableConstant ≥ (1 : ℝ), ∃ profileConstant ≥ (1 : ℝ),
      ∃ costMagnitude ≥ (1 : ℝ), ∃ leadingMagnitude ≥ (1 : ℝ), ∃ additiveMagnitude ≥ (0 : ℝ),
      let accuracy := 1 / (64 * (1 + profileConstant))
      let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
        (accuracy / 3) * additiveMagnitude)
      1 ≤ profileMagnitude ∧
      ∃ fullProfileConstant ≥ (1 : ℝ), ∃ sourceMagnitude ≥ (1 : ℝ),
      ∃ rootMin ≥ (8 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ endpointSize > (0 : ℝ),
      ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
      1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
      ∃ ratioMin ≥ (2 : ℝ),
      ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
      ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
      ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
      ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant timingError : ℝ),
      1 ≤ boundaryConstant → 0 ≤ timingError →
      (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ (index : Fin count) (nonterminal : index.val + 1 < count),
      ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
      let changed : Scales := {scales with frequency := frequency}
      let motion := prepared.trajectory.movingFamily.patchMotion
      (∀ source : Fin count, index.val < source.val →
        let length := changed.length (source.val + 1)
        0 ≤ entry source ∧ entry source ≤ path.stop ∧ 512 ≤ initialDistance source ∧
        initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
        ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
        ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
        (3 / 4 : ℝ) * length * initialDistance source ≤
          (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
            secondDipoleCenter motion (entry source) source)).re ∧
        ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
          (5 / 4 : ℝ) * length * initialDistance source) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source),
        (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
          quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
            extent * changed.length (source.val + 1)) ∧
        (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
          extent * changed.length (source.val + 1))) →
      ∀ magnitude : Fin count → ℝ,
      let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
        ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
      (∀ source : Fin count, index.val < source.val → 0 ≤ magnitude source ∧ ∀ time ∈ Icc 0 (entry source),
        sharpState source time ≤ magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))) →
      (∀ source : Fin count, index.val < source.val → magnitude source ≤ magnitudeMax) →
      (∀ source : Fin count, index.val < source.val → initialDistance source ≤ distanceMax) →
      (∀ source : Fin count, index.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
        motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
          (extent * changed.length (source.val + 1))) →
      ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
      |actualTime (index.val + 2) - changed.predictedTime sectionTime count (index.val + 2)| ≤
        timingError / changed.omega (index.val + 2) →
      (∀ source : Fin count, index.val < source.val →
        |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
          timingError / changed.omega (source.val + 1)) →
      (∀ source : Fin count, index.val < source.val → entry source ≤ entry ⟨index.val + 1, nonterminal⟩) →
      ∀ finish ∈ Icc 0 path.stop,
      (∀ time ∈ Icc 0 finish, |radialShape motion time index| ≤ 1 / 2) →
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let shape := fun time =>
        |(referenceStraightenedShape motion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape motion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|
      let origin := entry ⟨index.val + 1, nonterminal⟩
      changed.seed (index.val + 1) * Real.exp (growth * (finish - origin)) ≤ endpointSize →
      (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| < radius / 2) ∧
      ∃ lift : Fin 2 → ℝ → ℝ,
      (∀ side, Continuous (lift side) ∧ lift side 0 = phase (index.val + 1)) ∧
      (∀ side, ∀ time ∈ Icc 0 finish,
        positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index =
          (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time index‖ : ℂ) *
            Complex.exp (Complex.I * (lift side time : ℂ))) ∧
      let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
      let state := fun time => prepared.finiteCoordinateSize graph coordinate lift index time + raw time
      let sharp := fun time => prepared.rawSourceCenteredState time index +
        ‖relativeNormalizedFirstMoment changed motion prepared.reference index time‖ +
        ‖quadrupoleCenter motion time index - quadrupoleCenter prepared.reference time index‖ / changed.location (index.val + 1) + raw time
      let forcing := fun time => prepared.finiteCoordinateForeignForcing index time + prepared.physicalForeignSourceForcing index time
      ContinuousOn shape (Icc 0 finish) ∧ shape 0 = 0 ∧
      (∀ time ∈ Icc 0 finish,
        shape time < profileMagnitude * changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        shape time ≤ (profileMagnitude / 2) * changed.seed (index.val + 1) * Real.exp (growth * (time - origin))) ∧
      ContinuousOn state (Icc 0 finish) ∧ state 0 = 0 ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * state time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-growth * time) * forcing time) volume 0 finish ∧
      ∀ time ∈ Icc 0 finish,
        state time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) ∧
        sharp time ≤ fullProfileConstant * (2 * profileMagnitude + sourceMagnitude) *
          changed.seed (index.val + 1) * Real.exp (growth * (time - origin)) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, factors⟩ := exists_uniform_actual_domain_sharp_profile_bootstrap
  obtain ⟨inverseRadius, inversePositive, inverseConstant, inverseOne, inverse⟩ :=
    Section6.localNormalFormChart_exists_uniform_inverse_lipschitz graphAnalytic.contDiffAt coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, chartConstant, chartOne, thresholdMax, thresholdPositive, thresholdEighth,
    compatible, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, rootMin, rootEight,
    profileRadius, profilePositive, profileQuarter, profileEndpoint, profileEndpointPositive, profiles⟩ :=
    factors factorPositive factorSmall
  let accuracy := 1 / (64 * (1 + profileConstant))
  let profileMagnitude := 1 + 16 * (leadingMagnitude + accuracy * profileConstant * costMagnitude +
    (accuracy / 3) * additiveMagnitude)
  have magnitudePositive : 0 < profileMagnitude := zero_lt_one.trans_le magnitudeOne
  let radius := min profileRadius (inverseRadius / 2)
  have radiusPositive : 0 < radius := lt_min profilePositive (half_pos inversePositive)
  have radiusProfile : radius ≤ profileRadius := min_le_left _ _
  have radiusQuarter : radius ≤ 1 / 4 := radiusProfile.trans profileQuarter
  have radiusInverse : radius < inverseRadius := by
    have bound : radius ≤ inverseRadius / 2 := min_le_right _ _
    linarith only [bound, inversePositive]
  let endpointSize := min profileEndpoint (radius / (4 * inverseConstant * (1 + profileMagnitude)))
  have inversePositive' : 0 < inverseConstant := zero_lt_one.trans_le inverseOne
  have endpointPositive : 0 < endpointSize := by dsimp only [endpointSize]; positivity
  refine ⟨stableConstant, stableOne, profileConstant, profileOne, costMagnitude, costOne,
    leadingMagnitude, leadingOne, additiveMagnitude, additiveNonnegative, magnitudeOne,
    fullProfileConstant, fullProfileOne, sourceMagnitude, sourceOne, rootMin, rootEight,
    radius, radiusPositive, radiusQuarter, endpointSize, endpointPositive, ?_⟩
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨ratioMin, ratioTwo, profileScales⟩ :=
    profiles extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [profileScales scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant
      timingError boundaryOne timingNonnegative ratioSeparation,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < radius / 8),
    eventually_gt_atTop (0 : ℝ)] with frequency profileEstimate joint referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside radialSmall followerSmall sourceRates endpointBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let length := changed.length (index.val + 1)
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let seed := changed.seed (index.val + 1)
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let regularized := fun time => regularizedShapeCoordinates (length ^ 2 / 2) (1 / 16)
    (positiveHalfDiagonal motion time index) (negativeHalfDiagonal motion time index)
  let size := fun time => |(regularized time).1| + |(regularized time).2|
  have lengthPositive : 0 < length := changed.length_pos _
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have growthPositive : 0 < growth := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
    dsimp only [growth]
    positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have referenceBound (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape reference time index| + |stableShape reference time index| < radius / 8 := by
    have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
      ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ index
    change |diagonalDifference reference time index / length ^ 2 - 1| +
      |unstableShape reference time index| + |stableShape reference time index| < radius / 8 at actual
    linarith only [actual, abs_nonneg (diagonalDifference reference time index / length ^ 2 - 1)]
  have diagonal := joint prepared.toCascadeMaterialPreparedPair path
    (thresholdBound.trans (thresholdEighth.trans (by norm_num))) (factorSmall.trans (by norm_num))
    index nonterminal finish finishInside.1 finishInside.2 radialSmall
  have denominatorLower (time : ℝ) (inside : time ∈ Icc 0 finish) :
      length ^ 2 / 2 ≤ ‖positiveHalfDiagonal motion time index‖ ^ 2 := by
    have lower := (abs_le.mp (diagonal time inside).1).1
    change -(1 / 4 : ℝ) ≤ diagonalDifference motion time index / length ^ 2 - 1 at lower
    have ratioLower : (1 / 2 : ℝ) ≤ diagonalDifference motion time index / length ^ 2 := by linarith only [lower]
    have product := (le_div_iff₀ (sq_pos_of_pos lengthPositive)).mp ratioLower
    dsimp only [diagonalDifference] at product
    nlinarith only [product, sq_nonneg ‖negativeHalfDiagonal motion time index‖]
  obtain ⟨positiveContinuous, negativeContinuous, regularizedContinuous, initialUpper, initialSize⟩ :=
    actual_initial_regularized_geometry prepared.toCascadeMaterialPreparedPair index nonterminal
      radiusPositive radiusQuarter (denominatorLower 0 ⟨le_rfl, finishInside.1⟩)
      (referenceBound 0 ⟨le_rfl, finishInside.1⟩)
  change Continuous regularized at regularizedContinuous
  change size 0 < radius at initialSize
  have sizeContinuous : Continuous size := regularizedContinuous.fst.abs.add regularizedContinuous.snd.abs
  have agreement (terminal : ℝ) (inside : terminal ∈ Icc 0 finish)
      (prefixControl : ∀ current ∈ Icc 0 terminal, size current ≤ radius) :
      ∀ current ∈ Icc 0 terminal, regularized current =
        (unstableShape motion current index, stableShape motion current index) := by
    have subset : Icc (0 : ℝ) terminal ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    exact regularized_shape_prefix_eq_paper motion index (by positivity : 0 < length ^ 2 / 2)
      (positiveContinuous.continuousOn.mono subset) (negativeContinuous.continuousOn.mono subset)
      (fun current member => denominatorLower current (subset member)) initialUpper
      (fun current member => (prefixControl current member).trans radiusQuarter)
  have exposureAt (terminal : ℝ) (inside : terminal ∈ Icc 0 finish) :
      seed * Real.exp (growth * (terminal - origin)) ≤ endpointSize :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans endpointBound
  have profilesAt (terminal : ℝ) (inside : terminal ∈ Icc 0 finish)
      (small : ∀ current ∈ Icc 0 terminal,
        |unstableShape motion current index| + |stableShape motion current index| ≤ radius) :=
    profileEstimate count phase dipoleAngle prepared path index nonterminal entry initialDistance direction entries extents
      magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
      terminal ⟨inside.1, inside.2.trans finishInside.2⟩
      (fun current member => radialSmall current ⟨member.1, member.2.trans inside.2⟩)
      (fun current member => (small current member).trans radiusProfile)
      (fun receiver below current member => (followerSmall receiver below current ⟨member.1, member.2.trans inside.2⟩).trans radiusProfile)
      sourceRates ((exposureAt terminal inside).trans (min_le_left _ _))
  have endpointCoefficient : inverseConstant * (profileMagnitude / 2) * endpointSize ≤ radius / 8 := by
    have scaled := mul_le_mul_of_nonneg_left (min_le_right profileEndpoint (radius / (4 * inverseConstant * (1 + profileMagnitude))))
      (by positivity : 0 ≤ 4 * inverseConstant * (1 + profileMagnitude))
    have identity : (4 * inverseConstant * (1 + profileMagnitude)) *
        (radius / (4 * inverseConstant * (1 + profileMagnitude))) = radius := by field_simp
    rw [identity] at scaled
    have slack : 0 ≤ inverseConstant * endpointSize := mul_nonneg inversePositive'.le endpointPositive.le
    change 4 * inverseConstant * (1 + profileMagnitude) * endpointSize ≤ radius at scaled
    linear_combination (1 / 8 : ℝ) * scaled + (1 / 2 : ℝ) * slack
  have improve (terminal : ℝ) (inside : terminal ∈ Icc 0 finish)
      (prefixControl : ∀ current ∈ Icc 0 terminal, size current ≤ radius) : size terminal < radius / 2 := by
    have identity := agreement terminal inside prefixControl
    have targetSmall (current : ℝ) (member : current ∈ Icc 0 terminal) :
        |unstableShape motion current index| + |stableShape motion current index| ≤ radius := by
      simpa only [size, identity current member] using prefixControl current member
    obtain ⟨lift, _, _, _, _, shapeBounds, _, _, _, _, _⟩ := profilesAt terminal inside targetSmall
    have bound := (shapeBounds terminal ⟨inside.1, le_rfl⟩).2
    let shape := |(referenceStraightenedShape motion graph coordinate index terminal).1 -
        (referenceStraightenedShape reference graph coordinate index terminal).1| +
      |(referenceStraightenedShape motion graph coordinate index terminal).2 -
        (referenceStraightenedShape reference graph coordinate index terminal).2|
    change shape ≤ (profileMagnitude / 2) * seed * Real.exp (growth * (terminal - origin)) at bound
    have shapeBound : shape ≤ (profileMagnitude / 2) * endpointSize := by
      apply bound.trans
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (exposureAt terminal inside)
        (by positivity : 0 ≤ profileMagnitude / 2)
    have actualSmall : |unstableShape motion terminal index| + |stableShape motion terminal index| < radius / 2 :=
      physical_shape_strict_improvement radiusPositive radiusInverse (zero_le_one.trans inverseOne) inverse
        (targetSmall terminal ⟨inside.1, le_rfl⟩) (referenceBound terminal inside) shapeBound
        (by simpa only [mul_assoc] using endpointCoefficient)
    simpa only [size, identity terminal ⟨inside.1, le_rfl⟩] using actualSmall
  have confined := strictly_negative_of_prefix_improvement (sizeContinuous.continuousOn.sub continuousOn_const)
    (sub_neg.mpr initialSize) (by
      intro terminal inside prefixControl
      have improved := improve terminal inside (fun current member => sub_nonpos.mp (prefixControl current member))
      exact sub_neg.mpr (improved.trans (half_lt_self radiusPositive)))
  have prefixAt (terminal : ℝ) (inside : terminal ∈ Icc 0 finish) :
      ∀ current ∈ Icc 0 terminal, size current ≤ radius := by
    intro current member
    exact (sub_neg.mp (confined current ⟨member.1, member.2.trans inside.2⟩)).le
  have physicalSmall (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape motion time index| + |stableShape motion time index| < radius / 2 := by
    have identity := agreement time inside (prefixAt time inside) time ⟨inside.1, le_rfl⟩
    simpa only [size, identity] using improve time inside (prefixAt time inside)
  refine ⟨physicalSmall, ?_⟩
  exact profilesAt finish ⟨finishInside.1, le_rfl⟩ (fun time inside =>
    (physicalSmall time inside).le.trans (by linarith only [radiusPositive]))

end EulerNonuniqueness.Paper
