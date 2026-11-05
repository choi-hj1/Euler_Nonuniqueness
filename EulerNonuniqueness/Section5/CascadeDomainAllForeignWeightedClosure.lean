import EulerNonuniqueness.Section5.CascadeMixedAllForeignClosedWeightedForcing
import EulerNonuniqueness.Section5.CascadeCalibratedKnownSourceBudgetFromDomains

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_domain_all_foreign_weighted_closure
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∃ commonIncoming ≥ (0 : ℝ), ∃ commonOutgoing ≥ (0 : ℝ),
    ∃ sharpIncoming ≥ (0 : ℝ), ∃ sharpOutgoing ≥ (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ followerConstant ≥ (1 : ℝ),
    ∃ rootMin ≥ (8 : ℝ),
    let sourceMagnitude := 1 + 8 * (4 * sharpOutgoing + 1) +
      32 * followerConstant * (4 * commonOutgoing + 1)
    ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate →
    ∃ ratioMin ≥ max 2 (4 * followerConstant),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant tolerance timingError : ℝ),
    1 ≤ boundaryConstant → 0 < tolerance → 0 ≤ timingError →
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
    (∀ time ∈ Icc 0 finish, |unstableShape motion time index| + |stableShape motion time index| ≤ radius) →
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
    let allForeign := prepared.selectedForeignForcing (Finset.univ.erase index) index
    let origin := entry ⟨index.val + 1, nonterminal⟩
    ContinuousOn allForeign (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * shape time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * allForeign time) volume 0 finish ∧
    (∀ time ∈ Icc 0 finish, prepared.finiteCoordinateForeignForcing index time +
      prepared.physicalForeignSourceForcing index time ≤ allForeign time) ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * allForeign time) ≤
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * shape time) +
        sourceMagnitude * changed.seed (index.val + 1) * Real.exp (-growth * origin) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, factories⟩ :=
    exists_uniform_actual_mixed_all_foreign_closed_weighted_forcing
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive,
    commonIncoming, commonIncomingNonnegative, commonOutgoing, commonOutgoingNonnegative,
    sharpIncoming, sharpIncomingNonnegative, sharpOutgoing, sharpOutgoingNonnegative, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, followerConstant, followerOne, parentRatio, parentMinimum,
    rootMin, rootEight, estimates⟩ := factories factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, followerConstant, followerOne, rootMin, rootEight, ?_⟩
  dsimp only
  obtain ⟨_, calibrations⟩ := exists_uniform_calibrated_timed_known_source_budget_of_domains
    sharpIncomingNonnegative sharpOutgoingNonnegative commonIncomingNonnegative commonOutgoingNonnegative
    (zero_le_one.trans followerOne)
  intro extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive
  obtain ⟨calibratedRatio, _, domainsFactory⟩ := calibrations extent magnitudeMax distanceMax sourceRate extentOne
    magnitudeNonnegative distanceNonnegative sourceRatePositive
  let ratioMin := max parentRatio calibratedRatio
  refine ⟨ratioMin, parentMinimum.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant tolerance timingError
    boundaryOne tolerancePositive timingErrorNonnegative ratioSeparation
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have growthOne : 1 ≤ 2 * Real.sqrt 2 := by
    have lower : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    linarith only [lower]
  filter_upwards [estimates scales scaleRoot rootLarge amplitudeIdentity ((le_max_left _ _).trans ratioLarge)
      alphaPositive extent extentOne referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
      orbit sectionTime boundaryConstant tolerance boundaryOne tolerancePositive,
    domainsFactory scales amplitudePositive ((le_max_right _ _).trans ratioLarge) alphaPositive alphaSmall ratioPower
      (2 * Real.sqrt 2) timingError growthOne timingErrorNonnegative ratioSeparation sectionTime scaleRoot boundaryConstant
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    eventually_ge_atTop (1 : ℝ)] with frequency estimate domainEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
    entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside radialSmall targetSmall followerSmall sourceRates
  let changed : Scales := {scales with frequency := frequency}
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by
    have large := ((le_max_left _ _).trans parentMinimum).trans ((le_max_left _ _).trans ratioLarge)
    change 0 < scales.ratio
    linarith only [large]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have omegaGrowth : changed.omega (index.val + 1) ≤ 2 * Real.sqrt 2 * changed.omega (index.val + 1) := by
    have lower : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    nlinarith only [omegaPositive, mul_nonneg omegaPositive.le (sub_nonneg.mpr lower)]
  have actual := estimate count phase dipoleAngle prepared path index nonterminal path.stop path.stopPositive.le le_rfl
    entry initialDistance direction entries extents sourceRate sourceRatePositive magnitude sourceProfiles finish finishInside
    radialSmall targetSmall followerSmall (2 * Real.sqrt 2 * changed.omega (index.val + 1)) omegaGrowth sourceRates
  dsimp only at actual
  rw [← prepared.referenceIdentity] at actual
  obtain ⟨allContinuous, _, shapeIntegrable, allIntegrable, literalBound, forcingBound⟩ := actual
  have known := domainEstimate count (thresholdBound.trans (thresholdEighth.trans (by norm_num)))
    (factorSmall.trans (by norm_num)) prepared path index nonterminal entry initialDistance magnitude actualTime timeIdentity
    (fun source below => ⟨(entries source below).1, (entries source below).2.1⟩) nearestTiming sourceTiming timeOrder
    (fun source below => ⟨(sourceProfiles source below).1, magnitudeUpper source below⟩)
    (fun source below => ⟨(by norm_num : (0 : ℝ) ≤ 512).trans (entries source below).2.2.1, distanceUpper source below⟩)
    domains finish
  refine ⟨allContinuous, shapeIntegrable, allIntegrable, literalBound, ?_⟩
  have knownBound := add_le_add_left known.2
    (tolerance * (∫ time in (0 : ℝ)..finish,
      Real.exp (-(2 * Real.sqrt 2 * changed.omega (index.val + 1)) * time) *
        (|(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
        |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
          (referenceStraightenedShape prepared.reference graph coordinate index time).2|)))
  exact forcingBound.trans (by simpa only [add_assoc] using knownBound)

end EulerNonuniqueness.Paper
