import EulerNonuniqueness.Section5.CascadeGivenMapPostHitFollowerSmall
import EulerNonuniqueness.Section5.CascadeJointCoarserMonitorGeometry
import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.General.StrictPrefixBootstrap

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem post_hit_physical_shape_strict_improvement
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

private theorem post_hit_straightened_difference_le_full
    {cap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
    {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}
    (prepared : CascadeSourcePreparedPair cap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (graph coordinate : ℝ → ℝ) (lift : Fin 2 → ℝ → ℝ) (index : Fin count) (time : ℝ) :
    |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).1 -
        (referenceStraightenedShape prepared.reference graph coordinate index time).1| +
      |(referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time).2 -
        (referenceStraightenedShape prepared.reference graph coordinate index time).2| ≤
      prepared.finiteCoordinateSize graph coordinate lift index time +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
  have locationPositive := scales.location_pos (index.val + 1)
  have lengthPositive := scales.length_pos (index.val + 1)
  have rawNonnegative : 0 ≤ ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
    apply Finset.sum_nonneg
    intro patch _
    dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have extraNonnegative : 0 ≤
      |diagonalDifference prepared.trajectory.movingFamily.patchMotion time index - diagonalDifference prepared.reference time index| /
          scales.length (index.val + 1) ^ 2 +
        |relativeCorrectedPaperPhase (Section6.phaseCorrection 1 graph) lift
          (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) index time| +
        ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖ +
        ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index - quadrupoleCenter prepared.reference time index‖ /
          scales.location (index.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by positivity
  dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize]
  linarith only [extraNonnegative]

theorem exists_uniform_actual_joint_post_hit_follower_bootstrap
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ precision > (0 : ℝ), ∀ span ≥ (0 : ℝ), ∀ currentMagnitude ≥ (0 : ℝ),
    ∀ extent magnitudeMax distanceMax sourceRate : ℝ,
    1 ≤ extent → 0 ≤ magnitudeMax → 0 ≤ distanceMax → 0 < sourceRate → sourceRate < 1 / 8 →
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
      ∀ finish ∈ Icc 0 path.stop, ∀ hit ∈ Icc 0 path.stop,
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let origin := entry ⟨index.val + 1, nonterminal⟩
      origin ≤ hit → changed.omega (index.val + 1) * (finish - hit) ≤ span →
      (∀ time ∈ Icc 0 hit, sharpState index time ≤ currentMagnitude * changed.seed (index.val + 1) *
        Real.exp (growth * (time - origin))) →
      changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) ≤ 1 →
      (∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
        (|unstableShape motion time receiver| + |stableShape motion time receiver| < radius / 2) ∧
        |radialShape motion time receiver| < 1 / 8) ∧
      ∃ lift : Fin count → Fin 2 → ℝ → ℝ,
        (∀ receiver side, Continuous (lift receiver side) ∧ lift receiver side 0 = phase (receiver.val + 1)) ∧
        (∀ receiver : Fin count, receiver.val < index.val → ∀ side, ∀ time ∈ Icc 0 finish,
          positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver =
            (‖positiveHalfDiagonal (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver‖ : ℂ) *
              Complex.exp (Complex.I * (lift receiver side time : ℂ))) ∧
        ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
          prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
            ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤ precision := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, factors⟩ :=
    exists_uniform_actual_given_map_post_hit_follower_small graphAnalytic coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  obtain ⟨inverseRadius, inverseRadiusPositive, inverseConstant, inverseOne, inverse⟩ :=
    Section6.localNormalFormChart_exists_uniform_inverse_lipschitz graphAnalytic.contDiffAt coordinateSmooth
      graphZero coordinateZero graphDerivative coordinateDerivative
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨weakRadius, weakRadiusPositive, weakRadiusQuarter, rootMin, rootEight, parameters⟩ :=
    factors factor factorPositive factorSmall
  let radius := min weakRadius (inverseRadius / 2)
  have radiusPositive : 0 < radius := lt_min weakRadiusPositive (half_pos inverseRadiusPositive)
  have radiusWeak : radius ≤ weakRadius := min_le_left _ _
  have radiusQuarter : radius ≤ 1 / 4 := radiusWeak.trans weakRadiusQuarter
  have radiusInverse : radius < inverseRadius := by
    have bound : radius ≤ inverseRadius / 2 := min_le_right _ _
    linarith only [bound, inverseRadiusPositive]
  have inversePositive : 0 < inverseConstant := zero_lt_one.trans_le inverseOne
  let geometricPrecision := radius / (32 * inverseConstant)
  have geometricPrecisionPositive : 0 < geometricPrecision := by dsimp only [geometricPrecision]; positivity
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro precision precisionPositive
  let selectedPrecision := min precision geometricPrecision
  have selectedPositive : 0 < selectedPrecision := lt_min precisionPositive geometricPrecisionPositive
  intro span spanNonnegative currentMagnitude currentNonnegative extent magnitudeMax distanceMax sourceRate
    extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  obtain ⟨ratioMin, ratioTwo, scalesFactory⟩ := parameters currentMagnitude currentNonnegative selectedPrecision selectedPositive
    span spanNonnegative extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 2 := (thresholdBound.trans thresholdEighth).trans (by norm_num)
  filter_upwards [scalesFactory scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
      boundaryOne timingNonnegative ratioSeparation,
    scales.eventually_actual_joint_coarser_monitor_geometry amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) referenceNonnegative radiusPositive radiusQuarter,
    scales.eventually_rhombus_joint_diagonal_neutral_continuation amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne),
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative
      (by positivity : 0 < radius / 8), eventually_gt_atTop (0 : ℝ)]
    with frequency profileEstimate monitorGeometry joint referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside hit hitInside sourceRates originBefore shortSpan currentProfile exposureHit
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let observed := jointCoarserMonitor changed motion index radius
  have omegaPositive := changed.omega_pos frequencyPositive
    (by change 0 < scales.ratio; linarith only [ratioBound]) (index.val + 1)
  obtain ⟨monitorContinuous, monitorInitial, paperSmall⟩ := monitorGeometry prepared.toCascadeMaterialPreparedPair path
    factorPositive (factorSmall.trans (by norm_num)) thresholdSmall index
  have profilesAt (terminal : ℝ) (inside : terminal ∈ Icc 0 finish)
      (weak : ∀ current ∈ Icc 0 terminal, ∀ label, observed label current ≤ 0) :=
    profileEstimate count phase dipoleAngle prepared path index nonterminal entry initialDistance direction entries extents magnitude
      sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming sourceTiming timeOrder terminal
      ⟨inside.1, inside.2.trans finishInside.2⟩ hit hitInside
      (fun receiver below current member => (paperSmall terminal ⟨inside.1, inside.2.trans finishInside.2⟩ weak
        receiver below current member).trans radiusWeak) sourceRates originBefore
      ((mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 hit) omegaPositive.le).trans shortSpan) currentProfile exposureHit
  have referenceBound (receiver : Fin count) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape prepared.reference time receiver| + |stableShape prepared.reference time receiver| < radius / 8 := by
    have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time
      ⟨inside.1, inside.2.trans (finishInside.2.trans path.stopBound)⟩ receiver
    linarith only [actual, abs_nonneg (diagonalDifference prepared.reference time receiver / changed.length (receiver.val + 1) ^ 2 - 1)]
  have coefficientSmall : inverseConstant * selectedPrecision ≤ radius / 8 := by
    have scaled := mul_le_mul_of_nonneg_left (min_le_right precision geometricPrecision) inversePositive.le
    have identity : inverseConstant * geometricPrecision = radius / 32 := by
      dsimp only [geometricPrecision]
      field_simp
      ring
    rw [identity] at scaled
    linarith only [scaled, radiusPositive]
  have physicalAt (terminal : ℝ) (inside : terminal ∈ Icc 0 finish)
      (weak : ∀ current ∈ Icc 0 terminal, ∀ label, observed label current ≤ 0) :
      ∀ receiver : Fin count, receiver.val < index.val →
        |unstableShape motion terminal receiver| + |stableShape motion terminal receiver| < radius / 2 := by
    obtain ⟨lift, _, _, fullBound⟩ := profilesAt terminal inside weak
    intro receiver below
    have chartBound := (post_hit_straightened_difference_le_full prepared graph coordinate (lift receiver) receiver terminal).trans
      (fullBound terminal ⟨inside.1, le_rfl⟩ receiver below)
    exact post_hit_physical_shape_strict_improvement
      (first := (unstableShape motion terminal receiver, stableShape motion terminal receiver))
      (second := (unstableShape prepared.reference terminal receiver, stableShape prepared.reference terminal receiver))
      radiusPositive radiusInverse inversePositive.le inverse
      (paperSmall terminal ⟨inside.1, inside.2.trans finishInside.2⟩ weak receiver below terminal ⟨inside.1, le_rfl⟩)
      (referenceBound receiver terminal inside) chartBound coefficientSmall
  have monitorStrict := EulerNonuniqueness.General.finite_strictly_negative_of_strict_prefix_improvement
    (fun label => (monitorContinuous label).mono (Icc_subset_Icc le_rfl finishInside.2)) monitorInitial (by
      intro terminal inside weak _ label
      cases label with
      | none => norm_num [observed, jointCoarserMonitor]
      | some pair =>
        obtain ⟨receiver, side⟩ := pair
        have physical := physicalAt terminal inside weak receiver.val receiver.property
        have radialStrict : |radialShape motion terminal receiver.val| < radius / 2 := by
          rw [radialShape_eq_unstable_add_stable]
          exact (abs_add _ _).trans_lt physical
        fin_cases side
        · change |radialShape motion terminal receiver.val| - 1 / 2 < 0
          linarith only [radialStrict, radiusQuarter]
        · have radialPrefix (current : ℝ) (member : current ∈ Icc 0 terminal) :
              |radialShape motion current receiver.val| ≤ 1 / 2 := by
            have bound := weak current member (some (receiver, 0))
            change |radialShape motion current receiver.val| - 1 / 2 ≤ 0 at bound
            linarith only [bound]
          have diagonal := joint prepared.toCascadeMaterialPreparedPair path thresholdSmall
            (factorSmall.trans (by norm_num)) receiver.val (by omega) terminal inside.1
            (inside.2.trans finishInside.2) radialPrefix
          have lower := (abs_le.mp (diagonal terminal ⟨inside.1, le_rfl⟩).1).1
          have floor : changed.length (receiver.val.val + 1) ^ 2 / 2 ≤ ‖positiveHalfDiagonal motion terminal receiver.val‖ ^ 2 := by
            have ratio : (1 / 2 : ℝ) ≤ diagonalDifference motion terminal receiver.val / changed.length (receiver.val.val + 1) ^ 2 := by
              linarith only [lower]
            have product := (le_div_iff₀ (sq_pos_of_pos (changed.length_pos _))).mp ratio
            dsimp only [diagonalDifference] at product
            nlinarith only [product, sq_nonneg ‖negativeHalfDiagonal motion terminal receiver.val‖]
          have weakSize := weak terminal ⟨inside.1, le_rfl⟩ (some (receiver, 1))
          change _ - radius ≤ 0 at weakSize
          have regularizedSmall :
              |(regularizedShapeCoordinates (changed.length (receiver.val.val + 1) ^ 2 / 2) (1 / 16)
                (positiveHalfDiagonal motion terminal receiver.val) (negativeHalfDiagonal motion terminal receiver.val)).1| +
              |(regularizedShapeCoordinates (changed.length (receiver.val.val + 1) ^ 2 / 2) (1 / 16)
                (positiveHalfDiagonal motion terminal receiver.val) (negativeHalfDiagonal motion terminal receiver.val)).2| ≤ 1 / 4 := by
            linarith only [weakSize, radiusQuarter]
          have actualSmall := paperSmall terminal ⟨inside.1, inside.2.trans finishInside.2⟩ weak receiver.val receiver.property
            terminal ⟨inside.1, le_rfl⟩
          have upper := paper_shape_ratio_im_pos_of_small motion terminal receiver.val (actualSmall.trans radiusQuarter)
          have agreement := regularizedShapeCoordinates_eq_paper_of_small_upper motion terminal receiver.val floor regularizedSmall upper
          change _ - radius < 0
          rw [agreement]
          linarith only [physical, radiusPositive])
  have weakAll (terminal : ℝ) (inside : terminal ∈ Icc 0 finish) :
      ∀ current ∈ Icc 0 terminal, ∀ label, observed label current ≤ 0 := by
    intro current member label
    exact (monitorStrict current ⟨member.1, member.2.trans inside.2⟩ label).le
  have coarserPhysical : ∀ time ∈ Icc 0 finish, ∀ receiver : Fin count, receiver.val < index.val →
      (|unstableShape motion time receiver| + |stableShape motion time receiver| < radius / 2) ∧
        |radialShape motion time receiver| < 1 / 8 := by
    intro time inside receiver below
    have physical := physicalAt time inside (weakAll time inside) receiver below
    have radial := (abs_add (unstableShape motion time receiver) (stableShape motion time receiver)).trans_lt physical
    rw [← radialShape_eq_unstable_add_stable] at radial
    exact ⟨physical, radial.trans_le (by linarith only [radiusQuarter])⟩
  obtain ⟨lift, liftProperties, liftPolar, fullBound⟩ :=
    profilesAt finish ⟨finishInside.1, le_rfl⟩ (weakAll finish ⟨finishInside.1, le_rfl⟩)
  refine ⟨coarserPhysical, lift, liftProperties, liftPolar, ?_⟩
  intro time inside receiver below
  exact (fullBound time inside receiver below).trans (min_le_left precision geometricPrecision)

end EulerNonuniqueness.Paper
