import EulerNonuniqueness.Section5.CascadeGivenMapStrainRemainderWeightedSmall
import EulerNonuniqueness.Section5.CascadeCoarserSourceInputSmall
import EulerNonuniqueness.Section5.CascadeFullStatePhysicalRefinement

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_given_map_incoming_weighted_errors
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ rootMin ≥ (8 : ℝ),
    ∀ currentStateMagnitude currentSharpMagnitude : ℝ, 0 ≤ currentStateMagnitude → 0 ≤ currentSharpMagnitude →
    ∃ coarseFullPrecision > (0 : ℝ), ∃ endpoint > (0 : ℝ), endpoint ≤ 1 ∧
    ∀ extent magnitudeMax distanceMax coefficient : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < coefficient →
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
    (∀ current : Fin count, current.val ≤ receiver.val → ∀ time ∈ Icc 0 finish,
      |unstableShape motion time current| + |stableShape motion time current| ≤ 1 / 4) →
    ∀ suppliedLift : Fin 2 → ℝ → ℝ,
    (∀ side, ContinuousOn (suppliedLift side) (Icc 0 finish)) →
    (∀ side, suppliedLift side 0 = phase (receiver.val + 1)) →
    (∀ side, ∀ time ∈ Icc 0 finish,
      positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
        (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
          Complex.exp (Complex.I * (suppliedLift side time : ℂ))) →
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    (∀ source : Fin count, receiver.val < source.val → 2 * weight ≤ coefficient * changed.omega (source.val + 1)) →
    let stateBudget := fun time => prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch
    let origin := entry ⟨receiver.val + 1, nonterminal⟩
    (∀ time ∈ Icc 0 finish, stateBudget time ≤ currentStateMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    (∀ time ∈ Icc 0 finish, sharpState receiver time ≤ currentSharpMagnitude * changed.seed (receiver.val + 1) *
      Real.exp (weight * (time - origin))) →
    ∀ coarseLift : Fin count → Fin 2 → ℝ → ℝ,
    (∀ current : Fin count, current.val < receiver.val → ∀ time ∈ Icc 0 finish,
      prepared.finiteCoordinateSize graph coordinate (coarseLift current) current time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch ≤ coarseFullPrecision) →
    changed.seed (receiver.val + 1) * Real.exp (weight * (finish - origin)) ≤ endpoint →
    let remainder := relativeStraightenedSaddleStrainRemainder changed
      (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate receiver
    ContinuousOn remainder (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖remainder time‖) volume 0 finish ∧
    Real.exp (weight * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖remainder time‖) ≤
        (1 / 8) * changed.seed (receiver.val + 1) ∧
    let coarseInput := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver source time
    ContinuousOn coarseInput (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) • coarseInput time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖coarseInput time‖) volume 0 finish ∧
    Real.exp (weight * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖coarseInput time‖) ≤
        (1 / 8) * changed.seed (receiver.val + 1) := by
  classical
  obtain ⟨remainderThreshold, remainderThresholdPositive, remainderEighth, remainderCap, remainderCapPositive,
    remainderFactors⟩ := exists_uniform_actual_given_map_strain_remainder_weighted_small
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨coarseThreshold, coarseThresholdPositive, _, coarseCap, coarseCapPositive, coarseFactors⟩ :=
    exists_uniform_actual_coarser_source_input_small
  let rawCap := min remainderCap coarseCap
  let thresholdMax := min remainderThreshold coarseThreshold
  have capPositive : 0 < rawCap := lt_min remainderCapPositive coarseCapPositive
  have capRemainder : rawCap ≤ remainderCap := min_le_left _ _
  have capCoarse : rawCap ≤ coarseCap := min_le_right _ _
  refine ⟨thresholdMax, lt_min remainderThresholdPositive coarseThresholdPositive,
    (min_le_left _ _).trans remainderEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨remainderRadius, remainderRadiusPositive, _, remainderRoot, remainderRootEight, remainderParameters⟩ :=
    remainderFactors factor factorPositive factorSmall
  obtain ⟨coarseRadius, coarseRadiusPositive, _, coarseRoot, coarseRootEight, coarseParameters⟩ :=
    coarseFactors factorPositive factorSmall
  let radius := min remainderRadius coarseRadius
  have radiusPositive : 0 < radius := lt_min remainderRadiusPositive coarseRadiusPositive
  obtain ⟨coarseFullPrecision, coarseFullPositive, refinements⟩ := exists_uniform_actual_full_state_physical_refinement
    graphAnalytic.contDiffAt coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative radiusPositive
  let rootMin := max remainderRoot coarseRoot
  refine ⟨rootMin, remainderRootEight.trans (le_max_left _ _), ?_⟩
  intro currentStateMagnitude currentSharpMagnitude fullNonnegative sharpNonnegative
  obtain ⟨remainderEndpoint, remainderEndpointPositive, remainderFactory⟩ :=
    remainderParameters currentStateMagnitude fullNonnegative (1 / 8) (by norm_num)
  let endpoint := min remainderEndpoint (min 1 (coarseFullPrecision / (currentStateMagnitude + 1)))
  have endpointPositive : 0 < endpoint := by dsimp only [endpoint]; positivity
  have endpointRemainder : endpoint ≤ remainderEndpoint := min_le_left _ _
  have endpointOne : endpoint ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have endpointBudget : currentStateMagnitude * endpoint ≤ coarseFullPrecision := by
    have bound : endpoint ≤ coarseFullPrecision / (currentStateMagnitude + 1) :=
      (min_le_right _ _).trans (min_le_right _ _)
    have product := (le_div_iff₀ (by positivity : 0 < currentStateMagnitude + 1)).mp bound
    nlinarith only [product, endpointPositive]
  refine ⟨coarseFullPrecision, coarseFullPositive, endpoint, endpointPositive, endpointOne, ?_⟩
  intro extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨remainderRatio, remainderRatioTwo, remainderScales⟩ := remainderFactory extent magnitudeMax distanceMax coefficient
    extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  obtain ⟨coarseRatio, coarseRatioTwo, coarseScales⟩ := coarseParameters currentSharpMagnitude sharpNonnegative
    (1 / 8) (by norm_num) extent magnitudeMax distanceMax coefficient extentOne magnitudeNonnegative distanceNonnegative coefficientPositive
  let ratioMin := max remainderRatio coarseRatio
  refine ⟨ratioMin, remainderRatioTwo.trans (le_max_left _ _), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have remainderRatioLarge : remainderRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have coarseRatioLarge : coarseRatio ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := remainderRatioTwo.trans remainderRatioLarge
  filter_upwards [remainderScales scales scaleRoot ((le_max_left _ _).trans rootLarge) amplitudeIdentity remainderRatioLarge
      alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative referenceAmplitude threshold
      (thresholdBound.trans (min_le_left _ _)) orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    coarseScales scales scaleRoot ((le_max_right _ _).trans rootLarge) amplitudeIdentity coarseRatioLarge
      alphaPositive alphaSmall ratioPower referenceConstant referenceNonnegative referenceAmplitude threshold
      (thresholdBound.trans (min_le_right _ _)) orbit sectionTime boundaryConstant timingError boundaryOne timingNonnegative ratioSeparation,
    refinements scales ratioBound alphaPositive referenceConstant referenceNonnegative,
    eventually_gt_atTop (0 : ℝ)] with frequency remainderEstimate coarseEstimate refinement frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside knownSmall suppliedLift liftContinuous liftInitial liftPolar sourceRates
    fullProfile sharpProfile coarseLift coarseFull exposure
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let origin := entry ⟨receiver.val + 1, nonterminal⟩
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightPositive : 0 < weight := by
    have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
    dsimp only [weight]; positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have exposureAt (time : ℝ) (inside : time ∈ Icc 0 finish) : seed * Real.exp (weight * (time - origin)) ≤ endpoint :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) weightPositive.le)) seedPositive.le).trans exposure
  have targetFull (time : ℝ) (inside : time ∈ Icc 0 finish) :
      prepared.finiteCoordinateSize graph coordinate suppliedLift receiver time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ coarseFullPrecision := by
    have actual := fullProfile time inside
    change _ ≤ currentStateMagnitude * seed * Real.exp (weight * (time - origin)) at actual
    have scaled := mul_le_mul_of_nonneg_left (exposureAt time inside) fullNonnegative
    apply actual.trans
    simpa only [mul_assoc] using scaled.trans endpointBudget
  have physicalSmall (current : Fin count) (below : current.val ≤ receiver.val) :
      ∀ time ∈ Icc 0 finish, |unstableShape motion time current| + |stableShape motion time current| < radius := by
    have currentNonterminal : current.val + 1 < count := by omega
    by_cases equal : current = receiver
    · subst current
      exact refinement prepared path factorPositive receiver nonterminal finish finishInside
        (knownSmall receiver le_rfl) suppliedLift targetFull
    · have strictlyBelow : current.val < receiver.val := by
        have unequal : current.val ≠ receiver.val := by intro valueEqual; exact equal (Fin.ext valueEqual)
        omega
      exact refinement prepared path factorPositive current currentNonterminal finish finishInside
        (knownSmall current below) (coarseLift current) (coarseFull current strictlyBelow)
  have radialSmall (time : ℝ) (inside : time ∈ Icc 0 finish) : |radialShape motion time receiver| ≤ 1 / 2 := by
    rw [radialShape_eq_unstable_add_stable]
    exact (abs_add _ _).trans ((knownSmall receiver le_rfl time inside).trans (by norm_num))
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have sizeInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).finiteCoordinateSize = prepared.finiteCoordinateSize := rfl
  have remainderData := remainderEstimate count phase dipoleAngle (prepared.enlargeCap capRemainder) path receiver nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder finish finishInside radialSmall
    (fun current below time inside => (physicalSmall current below time inside).le.trans (min_le_left _ _))
    suppliedLift liftContinuous liftInitial liftPolar sourceRates
    (by simpa only [rawInvariant, sizeInvariant] using fullProfile) (exposure.trans endpointRemainder)
  dsimp only at remainderData
  have coarseData := coarseEstimate count phase dipoleAngle (prepared.enlargeCap capCoarse) path receiver nonterminal
    entry initialDistance direction entries extents magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles)
    magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder finish finishInside
    (fun current below time inside => (physicalSmall current below.le time inside).le.trans (min_le_right _ _))
    sourceRates (by simpa only [rawInvariant, centeredInvariant] using sharpProfile)
  dsimp only at coarseData
  exact ⟨remainderData.1, remainderData.2.1, remainderData.2.2, coarseData⟩

end EulerNonuniqueness.Paper
