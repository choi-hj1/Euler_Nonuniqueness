import EulerNonuniqueness.Section5.CascadeDomainAdditiveWeightedClosure
import EulerNonuniqueness.General.WeightedExponentialProfileBootstrap

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem domain_additive_seed_small_scalar
    {additiveAction stateAction ownMagnitude fullMagnitude magnitude precision seed weight origin : ℝ}
    (ownNonnegative : 0 ≤ ownMagnitude) (fullNonnegative : 0 ≤ fullMagnitude)
    (magnitudeNonnegative : 0 ≤ magnitude) (precisionPositive : 0 < precision) (seedNonnegative : 0 ≤ seed)
    (stateBound : stateAction ≤ magnitude * seed * Real.exp (-weight * origin))
    (additiveBound : additiveAction ≤ (precision / (1 + magnitude + (ownMagnitude + fullMagnitude) / 3)) * stateAction +
      (precision / (1 + magnitude + (ownMagnitude + fullMagnitude) / 3) / 3) *
        (ownMagnitude + fullMagnitude) * seed * Real.exp (-weight * origin)) :
    Real.exp (weight * origin) * additiveAction ≤ precision * seed := by
  let accuracy := precision / (1 + magnitude + (ownMagnitude + fullMagnitude) / 3)
  have accuracyNonnegative : 0 ≤ accuracy := by dsimp only [accuracy]; positivity
  have ratio : (magnitude + (ownMagnitude + fullMagnitude) / 3) /
      (1 + magnitude + (ownMagnitude + fullMagnitude) / 3) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith)
  have coefficient : accuracy * (magnitude + (ownMagnitude + fullMagnitude) / 3) ≤ precision := by
    convert mul_le_mul_of_nonneg_left ratio precisionPositive.le using 1 <;> dsimp only [accuracy] <;> ring
  have unweighted : additiveAction ≤ precision * seed * Real.exp (-weight * origin) := by
    have bounded := additiveBound.trans (add_le_add_right (mul_le_mul_of_nonneg_left stateBound accuracyNonnegative) _)
    apply bounded.trans
    convert mul_le_mul_of_nonneg_right coefficient (mul_nonneg seedNonnegative (Real.exp_pos (-weight * origin)).le) using 1 <;>
      dsimp only [accuracy] <;> ring
  have cancellation : Real.exp (weight * origin) * Real.exp (-weight * origin) = 1 := by
    rw [← Real.exp_add]; simp only [neg_mul, add_neg_cancel, Real.exp_zero]
  apply (mul_le_mul_of_nonneg_left unweighted (Real.exp_pos (weight * origin)).le).trans_eq
  calc
    _ = (precision * seed) * (Real.exp (weight * origin) * Real.exp (-weight * origin)) := by ring
    _ = _ := by rw [cancellation, mul_one]

theorem exists_uniform_actual_domain_additive_seed_small
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ coarseConstant ≥ (0 : ℝ), ∃ incomingConstant ≥ (0 : ℝ), ∃ outgoingConstant ≥ (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ fullCommonIncoming ≥ (0 : ℝ), ∃ fullCommonOutgoing ≥ (0 : ℝ),
    ∃ fullSharpIncoming ≥ (0 : ℝ), ∃ fullSharpOutgoing ≥ (0 : ℝ),
    ∃ toleranceControl : ℝ → ℝ → ℝ,
    (∀ stableConstant ≥ (0 : ℝ), ∀ accuracy > (0 : ℝ), 0 < toleranceControl stableConstant accuracy) ∧
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ responseE ≥ (1 : ℝ), ∃ fullFollower ≥ (1 : ℝ),
    ∃ rootMin ≥ (8 : ℝ),
    let ownFollower := coarseConstant * responseE / 8
    let ownMagnitude := 1 + 8 * (4 * outgoingConstant + 1) + 32 * ownFollower * (4 * commonOutgoing + 1)
    let fullMagnitude := 1 + 8 * (4 * fullSharpOutgoing + 1) + 32 * fullFollower * (4 * fullCommonOutgoing + 1)
    ∀ stableConstant ≥ (0 : ℝ),
    ∀ currentStateMagnitude ≥ (0 : ℝ), ∀ precision > (0 : ℝ),
    let accuracy := precision / (1 + currentStateMagnitude + (ownMagnitude + fullMagnitude) / 3)
    ∃ toleranceMax > (0 : ℝ), toleranceMax = toleranceControl stableConstant accuracy ∧
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
    ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant chartConstant tolerance timingError : ℝ),
    1 ≤ boundaryConstant → 0 ≤ chartConstant → 0 ≤ tolerance → tolerance ≤ toleranceMax → 0 ≤ timingError →
    (2 * Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ (receiver : Fin count) (nonterminal : receiver.val + 1 < count),
    ∀ entry initialDistance : Fin count → ℝ, ∀ direction : Fin count → ℂ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    (∀ source : Fin count, receiver.val < source.val →
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
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source),
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
    (∀ source : Fin count, receiver.val < source.val → 0 ≤ magnitude source ∧
      ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
        magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ source : Fin count, receiver.val < source.val → magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, receiver.val < source.val → initialDistance source ≤ distanceMax) →
    (∀ source : Fin count, receiver.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    ∀ actualTime : ℕ → ℝ, (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    |actualTime (receiver.val + 2) - changed.predictedTime sectionTime count (receiver.val + 2)| ≤
      timingError / changed.omega (receiver.val + 2) →
    (∀ source : Fin count, receiver.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, receiver.val < source.val → entry source ≤ entry ⟨receiver.val + 1, nonterminal⟩) →
    ∀ finish ∈ Icc 0 path.stop,
    (∀ time ∈ Icc 0 finish, |radialShape motion time receiver| ≤ 1 / 2) →
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let ownRadius := factor / 39321600 * changed.length (receiver.val + 1)
    let ownForcing := fun time => ∑ patch : Fin 4, ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖prepared.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid motion current receiver patch) ownRadius (power + 1) time -
        prepared.referenceWitness.trajectory.movingFamily.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver)
          (fun current => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion current receiver patch) ownRadius (power + 1) time‖
    let first := motion
    let second := prepared.reference
    let omega := changed.omega (receiver.val + 1)
    let length := changed.length (receiver.val + 1)
    let macroRadius := factor / 39321600 * changed.location (receiver.val + 1)
    let epsilon := changed.radius (receiver.val + 1) ^ 2 / length ^ 2
    let referenceSize := chartConstant * referenceConstant * ((changed.strain + changed.strain ^ 2) / omega + omega⁻¹ ^ 5)
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let shape := fun time => |(relative time).1| + |(relative time).2|
    let moment := fun time => ‖relativeNormalizedFirstMoment changed first second receiver time‖
    let center := fun time => prepared.rawSourceCenteredState time receiver
    let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let dilation := fun time => |diagonalDifference first time receiver - diagonalDifference second time receiver| / length ^ 2
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let difference := fun time => ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first receiver time macroRadius power -
      quadrupoleExteriorCoefficient changed second receiver time macroRadius power‖
    let forcing := fun time => |(leading time).2| + tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) + stableConstant * referenceSize * ‖leading time‖
    let additive := fun time => tolerance * (moment time + center time + shape time) +
      stableConstant * omega * epsilon * (center time + raw time) + stableConstant * epsilon * ownForcing time +
      stableConstant * (length / macroRadius) * (changed.strain * center time + difference time) +
      stableConstant * referenceSize * ‖leading time‖ + stableConstant * omega * referenceSize * dilation time
    let drive := fun time => ‖leading time‖ + (forcing time - |(leading time).2| + stableConstant * omega * referenceSize * dilation time)
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time + raw time
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time ∈ Icc 0 finish, stateBudget time ≤ currentStateMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    (∀ time : ℝ, additive time = drive time - ‖leading time‖) ∧
    (∀ time ∈ Icc 0 finish, 0 ≤ additive time) ∧ ContinuousOn additive (Icc 0 finish) ∧
    ContinuousOn stateBudget (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * additive time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * stateBudget time) volume 0 finish ∧
    Real.exp (weight * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * additive time) ≤
        precision * changed.seed (receiver.val + 1) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceControl, tolerancePositive, factors⟩ :=
    exists_uniform_actual_domain_additive_weighted_closure_factor_uniform graphAnalytic coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive,
    coarseConstant, coarseNonnegative, incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    fullCommonIncoming, fullCommonIncomingNonnegative, fullCommonOutgoing, fullCommonOutgoingNonnegative,
    fullSharpIncoming, fullSharpIncomingNonnegative, fullSharpOutgoing, fullSharpOutgoingNonnegative,
    toleranceControl, tolerancePositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne,
    rootMin, rootEight, factory⟩ := factors factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, responseE, responseEOne, fullFollower, fullFollowerOne, rootMin, rootEight, ?_⟩
  dsimp only
  let ownFollower := coarseConstant * responseE / 8
  let ownMagnitude := 1 + 8 * (4 * outgoingConstant + 1) + 32 * ownFollower * (4 * commonOutgoing + 1)
  let fullMagnitude := 1 + 8 * (4 * fullSharpOutgoing + 1) + 32 * fullFollower * (4 * fullCommonOutgoing + 1)
  have ownNonnegative : 0 ≤ ownMagnitude := by
    have responseNonnegative := zero_le_one.trans responseEOne
    dsimp only [ownMagnitude, ownFollower]
    positivity
  have fullNonnegative : 0 ≤ fullMagnitude := by
    have followerNonnegative := zero_le_one.trans fullFollowerOne
    dsimp only [fullMagnitude]
    positivity
  intro stableConstant stableNonnegative currentStateMagnitude currentNonnegative precision precisionPositive
  let accuracy := precision / (1 + currentStateMagnitude + (ownMagnitude + fullMagnitude) / 3)
  have accuracyPositive : 0 < accuracy := by dsimp only [accuracy]; positivity
  refine ⟨toleranceControl stableConstant accuracy,
    tolerancePositive stableConstant stableNonnegative accuracy accuracyPositive, rfl, ?_⟩
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨ratioMin, ratioTwo, estimates⟩ := factory stableConstant stableNonnegative accuracy accuracyPositive
    extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative
    referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant chartConstant tolerance timingError boundaryOne
    chartNonnegative toleranceNonnegative toleranceSmall timingErrorNonnegative ratioSeparation
  filter_upwards [estimates scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant chartConstant
      tolerance timingError boundaryOne chartNonnegative toleranceNonnegative toleranceSmall timingErrorNonnegative ratioSeparation]
    with frequency estimate
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  intro entries extents magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder
    finish finishInside radialSmall small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds currentProfile
  have data := estimate count phase dipoleAngle prepared path receiver nonterminal entry initialDistance direction entries extents
    magnitude profiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    radialSmall small suppliedLift suppliedContinuous suppliedInitial suppliedPolar rateBounds
  obtain ⟨identity, nonnegative, additiveContinuous, stateContinuous, additiveI, stateI, bound⟩ := data
  let changed : Scales := {scales with frequency := frequency}
  let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let origin := entry ⟨receiver.val + 1, nonterminal⟩
  have seedNonnegative : 0 ≤ changed.seed (receiver.val + 1) := by dsimp only [Scales.seed]; positivity
  have action := intervalIntegral.integral_exp_neg_mul_le_of_same_rate_majorant finishInside.1 stateI currentProfile
  have stateReduced : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch)) ≤
      currentStateMagnitude * changed.seed (receiver.val + 1) * Real.exp (-weight * origin) := by
    calc
      _ ≤ finish * (currentStateMagnitude * changed.seed (receiver.val + 1)) * Real.exp (-weight * origin) := action
      _ ≤ 1 * (currentStateMagnitude * changed.seed (receiver.val + 1)) * Real.exp (-weight * origin) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (finishInside.2.trans path.stopBound)
          (mul_nonneg currentNonnegative seedNonnegative)) (Real.exp_pos (-weight * origin)).le
      _ = _ := by ring
  refine ⟨identity, nonnegative, additiveContinuous, stateContinuous, additiveI, stateI, ?_⟩
  exact domain_additive_seed_small_scalar ownNonnegative fullNonnegative currentNonnegative precisionPositive
    seedNonnegative stateReduced bound

end EulerNonuniqueness.Paper

