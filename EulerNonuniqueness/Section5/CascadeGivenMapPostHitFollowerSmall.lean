import EulerNonuniqueness.Section5.CascadeGivenMapStrongFollowerPrefixResolvedSourceEnvelope
import EulerNonuniqueness.Section5.CascadeFullFollowerDriverSmall
import EulerNonuniqueness.Section5.CascadeShortMacroDriverSmall
import EulerNonuniqueness.Section1.SwitchedSourceResponseSeedSmall
import EulerNonuniqueness.Section1.OutgoingShortSourceActionSmall
import EulerNonuniqueness.Section6.SourcePacketBoundedRadiusNeutralSmall
import EulerNonuniqueness.General.ExponentialConvolutionSplit

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private def postHitOneBasedExtension {count : ℕ} (values : Fin count → ℝ) (index : ℕ) : ℝ :=
  if h : index - 1 < count then values ⟨index - 1, h⟩ else 0
private theorem postHitOneBasedExtension_apply {count : ℕ} (values : Fin count → ℝ) (index : Fin count) :
    postHitOneBasedExtension values (index.val + 1) = values index := by
  simp only [postHitOneBasedExtension, Nat.add_sub_cancel_right, index.isLt, dite_true]

theorem exists_uniform_actual_given_map_post_hit_follower_small
    {graph coordinate : ℝ → ℝ} (graphAnalytic : AnalyticAt ℝ graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) (graphZero : graph 0 = 0)
    (coordinateZero : coordinate 0 = 0) (graphDerivative : HasDerivAt graph 0 0)
    (coordinateDerivative : HasDerivAt coordinate 1 0) :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ currentMagnitude ≥ (0 : ℝ), ∀ precision > (0 : ℝ), ∀ span ≥ (0 : ℝ),
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
      (∀ receiver : Fin count, receiver.val < index.val → ∀ time ∈ Icc 0 finish,
        |unstableShape motion time receiver| + |stableShape motion time receiver| ≤ radius) →
      (∀ source : Fin count, index.val < source.val →
        2 * (2 * Real.sqrt 2 * changed.omega (index.val + 1)) ≤ sourceRate * changed.omega (source.val + 1)) →
      let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
      let origin := entry ⟨index.val + 1, nonterminal⟩
      origin ≤ hit → changed.omega (index.val + 1) * (finish - hit) ≤ span →
      (∀ time ∈ Icc 0 hit, sharpState index time ≤ currentMagnitude * changed.seed (index.val + 1) *
        Real.exp (growth * (time - origin))) →
      changed.seed (index.val + 1) * Real.exp (growth * (hit - origin)) ≤ 1 →
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
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, responseCap, responseCapPositive,
    incomingConstant, incomingNonnegative, outgoingConstant, outgoingNonnegative, factors⟩ :=
    exists_uniform_actual_given_map_strong_follower_prefix_resolved_source_envelope
      graphAnalytic coordinateSmooth graphZero coordinateZero graphDerivative coordinateDerivative
  obtain ⟨driverCap, driverCapPositive, drivers⟩ := exists_uniform_actual_full_follower_driver_small
  obtain ⟨shortCap, shortCapPositive, shortDrivers⟩ := exists_uniform_actual_short_macro_driver_small
  let rawCap := min responseCap (min driverCap shortCap)
  have capResponse : rawCap ≤ responseCap := min_le_left _ _
  have capDriver : rawCap ≤ driverCap := (min_le_right _ _).trans (min_le_left _ _)
  have capShort : rawCap ≤ shortCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap,
    lt_min responseCapPositive (lt_min driverCapPositive shortCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, constant, constantOne, comparison, comparisonOne,
    geometry, geometryOne, row, rowNonnegative, responseRatio, responseRatioBound,
    rootMin, rootEight, parameters⟩ := factors factor factorPositive factorSmall
  let multiplier := comparison * constant
  have multiplierPositive : 0 < multiplier := by dsimp only [multiplier]; positivity
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro currentMagnitude currentNonnegative precision precisionPositive span spanNonnegative
    extent magnitudeMax distanceMax sourceRate extentOne magnitudeNonnegative distanceNonnegative sourceRatePositive sourceRateSmall
  let preBudget := precision / (4 * (Real.exp span + 1))
  have prePositive : 0 < preBudget := by dsimp only [preBudget]; positivity
  let ratioMin := max responseRatio (4 * constant)
  refine ⟨ratioMin, (le_max_left (2 : ℝ) _).trans (responseRatioBound.trans (le_max_left _ _)), ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
    referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant timingError
    boundaryOne timingNonnegative ratioSeparation
  have responseRatioLarge : responseRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have fourConstant : 4 * constant ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := (le_max_left (2 : ℝ) _).trans (responseRatioBound.trans responseRatioLarge)
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have scalarSeparation : (Real.sqrt 2 + 1) * 8 ≤ scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) := by
    linarith only [ratioSeparation, Real.sqrt_nonneg (2 : ℝ)]
  let feedbackCap := multiplier * (row * geometry + geometry)
  have feedbackCapNonnegative : 0 ≤ feedbackCap := by dsimp only [feedbackCap]; positivity
  have rhoLimit := ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul 216360000).add
    ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul 576)
  simp only [mul_zero, zero_add] at rhoLimit
  filter_upwards [parameters extent extentOne 1 zero_lt_one scales scaleRoot rootLarge amplitudeIdentity responseRatioLarge alphaPositive
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne,
    drivers currentMagnitude multiplier row currentNonnegative multiplierPositive.le rowNonnegative preBudget prePositive
      scales amplitudePositive ratioBound alphaPositive orbit sectionTime factor scaleRoot boundaryConstant
      factorPositive factorSmall rootOne boundaryOne thresholdSmall referenceNonnegative,
    shortDrivers span multiplier row (precision / 4) spanNonnegative multiplierPositive.le rowNonnegative (by positivity)
      scales ratioBound alphaPositive,
    scales.eventually_switched_source_response_seed_small ratioBound alphaPositive alphaSmall ratioPower
      sourceRatePositive sourceRateSmall timingNonnegative scalarSeparation sectionTime incomingNonnegative outgoingNonnegative
      (zero_le_one.trans extentOne) magnitudeNonnegative distanceNonnegative (by norm_num : (0 : ℝ) ≤ 1)
      (show 0 < preBudget / multiplier by positivity),
    scales.eventually_outgoing_short_source_action_small ratioBound alphaPositive outgoingNonnegative spanNonnegative
      (show 0 < precision / (4 * multiplier) by positivity),
    scales.eventually_bounded_radius_source_neutral_small amplitudePositive ratioBound alphaPositive
      (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) (zero_lt_one.trans_le extentOne) zero_lt_one,
    rhoLimit.eventually (eventually_lt_nhds zero_lt_one), eventually_ge_atTop (4 * feedbackCap + 1)]
    with frequency response driverEstimate shortEstimate scalarEstimate outgoingEstimate neutral rhoSmall frequencyLarge
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal entry initialDistance direction
  dsimp only
  intro entries extents magnitude sourceProfiles magnitudeUpper distanceUpper domains actualTime timeIdentity nearestTiming
    sourceTiming timeOrder finish finishInside hit hitInside followerSmall sourceRates originBefore shortSpan currentProfile exposureHit
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (index.val + 1)
  let growth := 2 * Real.sqrt 2 * omega
  let origin := entry ⟨index.val + 1, nonterminal⟩
  let seed := changed.seed (index.val + 1)
  let rho := 216360000 * changed.hessian + 576 * changed.strain
  let rate := constant * omega / changed.ratio + multiplier * (row * geometry * rho + 1 * geometry)
  let finer := Finset.univ.filter (fun source : Fin count => index.val < source.val)
  let sourceEnvelope := fun time => ∑ source ∈ finer,
    if time ≤ entry source then incomingConstant * extent ^ 2 * changed.circulation (source.val + 1) * changed.length (source.val + 1) ^ 2 *
      (1 + (changed.location (source.val + 1))⁻¹) * magnitude source * Real.exp (sourceRate * changed.omega (source.val + 1) * (time - entry source))
    else outgoingConstant * changed.circulation (source.val + 1) * (changed.circulation (source.val + 1) * (time - entry source) +
      (1 + initialDistance source) * changed.length (source.val + 1) ^ 2 + ‖centroidAsymmetry motion (entry source) source‖)
  have frequencyPositive : 0 < frequency := by linarith only [frequencyLarge, feedbackCapNonnegative]
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have omegaLower : frequency ≤ omega := changed.omega_ge_frequency frequencyPositive
    (by change 1 ≤ scales.ratio; linarith only [ratioBound]) _
  have growthPositive : 0 < growth := by dsimp only [growth]; positivity
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have rhoNonnegative : 0 ≤ rho := by
    have hessian : 0 ≤ changed.hessian := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3)
    have strain : 0 ≤ changed.strain := tsum_nonneg fun source => div_nonneg
      (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
    dsimp only [rho]; positivity
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateBound : rate ≤ growth / 4 := by
    have coarse : constant * omega / changed.ratio ≤ omega / 4 := by
      apply (div_le_iff₀ ratioPositive).mpr
      change constant * omega ≤ omega / 4 * scales.ratio
      nlinarith only [mul_le_mul_of_nonneg_left fourConstant omegaPositive.le]
    have feedback : multiplier * (row * geometry * rho + 1 * geometry) ≤ feedbackCap := by
      have scaled := mul_le_mul_of_nonneg_left rhoSmall.le (show 0 ≤ row * geometry by positivity)
      change row * geometry * rho ≤ row * geometry * 1 at scaled
      dsimp only [feedbackCap]
      nlinarith only [mul_le_mul_of_nonneg_left scaled multiplierPositive.le]
    have cap : feedbackCap ≤ omega / 4 := by linarith only [frequencyLarge, omegaLower]
    have halfBound : rate ≤ omega / 2 := by
      calc
        _ ≤ omega / 4 + feedbackCap := add_le_add coarse feedback
        _ ≤ omega / 4 + omega / 4 := add_le_add_left cap _
        _ = omega / 2 := by ring
    have sqrtOne : (1 : ℝ) ≤ Real.sqrt 2 := by norm_num
    have growthBound : omega / 2 ≤ growth / 4 := by
      dsimp only [growth]
      nlinarith only [mul_le_mul_of_nonneg_right sqrtOne omegaPositive.le]
    exact halfBound.trans growthBound
  have rateOmega : rate ≤ omega := by
    have sqrtTwo : Real.sqrt 2 ≤ 2 := by norm_num [Real.sqrt_le_iff]
    have bound : growth / 4 ≤ omega := by dsimp only [growth]; nlinarith only [mul_le_mul_of_nonneg_right sqrtTwo omegaPositive.le]
    exact rateBound.trans bound
  have rawInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext time source patch
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have macroInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).macroSourceState = prepared.macroSourceState := by
    funext time source
    with_reducible_and_instances dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
  have driverInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).weightedMacroSourceState = prepared.weightedMacroSourceState := by
    funext time source
    simp only [CascadeSourcePreparedPair.weightedMacroSourceState, macroInvariant]
  obtain ⟨lift, liftProperties, liftPolar, responseData⟩ := response count phase dipoleAngle
    (prepared.enlargeCap capResponse) path index nonterminal finish finishInside.1 finishInside.2 entry initialDistance direction
    entries extents sourceRate sourceRatePositive magnitude (by simpa only [rawInvariant, centeredInvariant] using sourceProfiles) followerSmall
  dsimp only at responseData
  simp only [rawInvariant, driverInvariant] at responseData
  obtain ⟨_, _, _, _, _, _, _, _, _, sourceI, history⟩ := responseData
  let envelope := fun time => ‖fun receiver : Fin count => if receiver.val < index.val then
    changed.location (receiver.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) else 0‖
  let forcing := fun time => row * rho * prepared.weightedMacroSourceState time index + sourceEnvelope time
  have exposureAt (time : ℝ) (inside : time ∈ Icc 0 hit) : seed * Real.exp (growth * (time - origin)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 origin) growthPositive.le)) seedPositive.le).trans exposureHit
  have neutralBound (source : Fin count) (below : index.val < source.val) :
      ‖centroidAsymmetry motion (entry source) source‖ ≤ changed.length (source.val + 1) ^ 2 := by
    have actual := neutral prepared.toCascadeMaterialPreparedPair path
      (thresholdSmall.trans (by norm_num)) (factorSmall.trans (by norm_num)) source (entry source)
      (entries source below).1 (entries source below).2.1 (domains source below)
      (entry source) ⟨(entries source below).1, le_rfl⟩
    simpa only [one_mul] using actual
  let paper : Fin count → ℕ := fun source => source.val + 1
  have paperInjective : Function.Injective paper := by intro first second equal; apply Fin.ext; dsimp only [paper] at equal; omega
  let selected := finer.image paper
  let natMagnitude := postHitOneBasedExtension magnitude
  let natDistance := postHitOneBasedExtension initialDistance
  let natNeutral := postHitOneBasedExtension (fun source => ‖centroidAsymmetry motion (entry source) source‖)
  have originIdentity : actualTime (index.val + 2) = origin := by
    simpa only [origin] using timeIdentity ⟨index.val + 1, nonterminal⟩
  have natSourceEquality (time : ℝ) :
      (∑ source ∈ selected,
        if time ≤ actualTime source then incomingConstant * extent ^ 2 * changed.circulation source * changed.length source ^ 2 *
          (1 + (changed.location source)⁻¹) * natMagnitude source * Real.exp (sourceRate * changed.omega source * (time - actualTime source))
        else outgoingConstant * changed.circulation source * (changed.circulation source * (time - actualTime source) +
          (1 + natDistance source) * changed.length source ^ 2 + natNeutral source)) = sourceEnvelope time := by
    rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)]
    apply Finset.sum_congr rfl
    intro source _
    simp only [paper, timeIdentity, natMagnitude, natDistance, natNeutral, postHitOneBasedExtension_apply]
  have preBound (time : ℝ) (inside : time ∈ Icc 0 hit) :
      multiplier / changed.location (index.val + 1) ^ 4 * (∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * forcing current) ≤ 2 * preBudget := by
    have scalar := scalarEstimate count (index.val + 1) selected (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        dsimp only [paper]; omega) actualTime
      (by rw [originIdentity]; exact (entries ⟨index.val + 1, nonterminal⟩ (by simp)).1)
      nearestTiming (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        exact sourceTiming source (Finset.mem_filter.mp sourceMember).2)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        dsimp only [paper]
        rw [timeIdentity, originIdentity]
        exact ⟨(entries source finerSource).1, timeOrder source finerSource⟩)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have actual := sourceRates source (Finset.mem_filter.mp sourceMember).2
        have sqrtNonnegative := Real.sqrt_nonneg (2 : ℝ)
        have scaled := mul_nonneg sqrtNonnegative omegaPositive.le
        change Real.sqrt 2 * omega ≤ sourceRate * changed.omega (source.val + 1)
        linarith only [actual, scaled]) natMagnitude natDistance natNeutral
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        simpa only [paper, natMagnitude, postHitOneBasedExtension_apply] using
          ⟨(sourceProfiles source finerSource).1, magnitudeUpper source finerSource⟩)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        have nonnegative : 0 ≤ initialDistance source := by linarith only [(entries source finerSource).2.2.1]
        simpa only [paper, natDistance, postHitOneBasedExtension_apply] using ⟨nonnegative, distanceUpper source finerSource⟩)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        simpa only [paper, natNeutral, postHitOneBasedExtension_apply, one_mul] using
          ⟨norm_nonneg (centroidAsymmetry motion (entry source) source), neutralBound source finerSource⟩)
      rate time 1 rateNonnegative (by
        change rate ≤ Real.sqrt 2 * omega / 2
        change rate ≤ growth / 4 at rateBound
        dsimp only [growth] at rateBound
        linarith only [rateBound])
      inside.1 le_rfl (by simpa only [originIdentity] using exposureAt time inside)
    dsimp only at scalar

    have sourceKernelI : IntervalIntegrable (fun current => Real.exp (rate * (time - current)) * sourceEnvelope current) volume 0 time := by
      convert scalar.2.1 using 1
      funext current
      exact congrArg (fun value : ℝ => Real.exp (rate * (time - current)) * value) (natSourceEquality current).symm
    have sourceSmall : (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * sourceEnvelope current) /
        changed.location (index.val + 1) ^ 4 ≤ preBudget / multiplier := by
      convert scalar.2.2 using 1
      congr 1
      apply intervalIntegral.integral_congr
      intro current _
      exact congrArg (fun value : ℝ => Real.exp (rate * (time - current)) * value) (natSourceEquality current).symm
    have driver := driverEstimate count phase dipoleAngle (prepared.enlargeCap capDriver) path index time inside.1
      (inside.2.trans hitInside.2) origin rate rateNonnegative rateBound
      (by intro current member; simpa only [rawInvariant, centeredInvariant] using currentProfile current ⟨member.1, member.2.trans inside.2⟩)
      (exposureAt time inside)
    dsimp only at driver
    simp only [driverInvariant] at driver
    have split : (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current) =
        (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * row * rho * prepared.weightedMacroSourceState current index) +
        ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * sourceEnvelope current := by
      simp_rw [forcing, mul_add]
      rw [intervalIntegral.integral_add (by simpa only [mul_assoc] using driver.2.1) sourceKernelI]
      congr 1
      apply intervalIntegral.integral_congr
      intro current _
      ring
    rw [split, mul_add]
    have scaled := mul_le_mul_of_nonneg_left sourceSmall multiplierPositive.le
    have sourceBound : multiplier / changed.location (index.val + 1) ^ 4 *
        (∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * sourceEnvelope current) ≤ preBudget := by
      convert scaled using 1 <;> field_simp
    linarith only [driver.2.2.2, sourceBound]

  let outgoingSource := fun current => ∑ source ∈ selected,
    outgoingConstant * changed.circulation source * (changed.circulation source * (current - actualTime source) +
      (1 + natDistance source) * changed.length source ^ 2 + natNeutral source)
  have outgoingEquality (current : ℝ) (after : hit < current) : sourceEnvelope current = outgoingSource current := by
    dsimp only [sourceEnvelope, outgoingSource, selected]
    rw [Finset.sum_image (fun first _ second _ equal => paperInjective equal)]
    apply Finset.sum_congr rfl
    intro source member
    have finerSource := (Finset.mem_filter.mp member).2
    have inactive : ¬ current ≤ entry source := not_le_of_gt ((timeOrder source finerSource).trans originBefore |>.trans_lt after)
    simp only [paper, timeIdentity, natDistance, natNeutral, postHitOneBasedExtension_apply, inactive, ite_false]
  have postBound (time : ℝ) (inside : time ∈ Icc 0 finish) (after : hit < time) :
      multiplier / changed.location (index.val + 1) ^ 4 * (∫ current in hit..time,
        Real.exp (rate * (time - current)) * forcing current) ≤ precision / 2 := by
    have shortAt : omega * (time - hit) ≤ span :=
      (mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 hit) omegaPositive.le).trans shortSpan
    have outgoing := outgoingEstimate (index.val + 1) selected (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have := (Finset.mem_filter.mp sourceMember).2
        dsimp only [paper]; omega)
      actualTime natDistance natNeutral hit time rate hitInside.1 after.le
      (inside.2.trans (finishInside.2.trans path.stopBound)) (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        dsimp only [paper]; rw [timeIdentity]
        exact ⟨(entries source finerSource).1, (timeOrder source finerSource).trans originBefore⟩)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        have nonnegative : 0 ≤ initialDistance source := by linarith only [(entries source finerSource).2.2.1]
        simpa only [paper, natDistance, postHitOneBasedExtension_apply] using
          ⟨nonnegative, (entries source finerSource).2.2.2.1⟩)
      (by
        intro source member
        obtain ⟨source, sourceMember, rfl⟩ := Finset.mem_image.mp member
        have finerSource := (Finset.mem_filter.mp sourceMember).2
        simpa only [paper, natNeutral, postHitOneBasedExtension_apply] using
          ⟨norm_nonneg (centroidAsymmetry motion (entry source) source), neutralBound source finerSource⟩)
      rateNonnegative rateOmega shortAt
    dsimp only at outgoing
    have driver := shortEstimate (prepared.enlargeCap capShort) path index hit time rate
      hitInside.1 after.le (inside.2.trans finishInside.2) shortAt rateOmega
    dsimp only at driver
    simp only [driverInvariant] at driver
    have tailIdentity : (∫ current in hit..time, Real.exp (rate * (time - current)) * forcing current) =
        (∫ current in hit..time, Real.exp (rate * (time - current)) * row * rho * prepared.weightedMacroSourceState current index) +
        ∫ current in hit..time, Real.exp (rate * (time - current)) * outgoingSource current := by
      have equal : (∫ current in hit..time, Real.exp (rate * (time - current)) * forcing current) =
          ∫ current in hit..time,
            Real.exp (rate * (time - current)) * row * rho * prepared.weightedMacroSourceState current index +
              Real.exp (rate * (time - current)) * outgoingSource current := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun current member => by
          rw [uIoc_of_le after.le] at member
          dsimp only [forcing]
          rw [outgoingEquality current member.1]
          ring)
      rw [equal, intervalIntegral.integral_add driver.2.1 outgoing.2.1]
    rw [tailIdentity, mul_add]
    have scaled := mul_le_mul_of_nonneg_left outgoing.2.2.2 multiplierPositive.le
    have sourceBound : multiplier / changed.location (index.val + 1) ^ 4 *
        (∫ current in hit..time, Real.exp (rate * (time - current)) * outgoingSource current) ≤ precision / 4 := by
      convert scaled using 1 <;> field_simp <;> ring
    linarith only [driver.2.2, sourceBound]
  have budgetIdentity : (Real.exp span + 1) * (2 * preBudget) = precision / 2 := by
    dsimp only [preBudget]
    field_simp
    ring
  have budgetNonnegative : 0 ≤ 2 * preBudget := by positivity
  have prePlain : 2 * preBudget ≤ precision / 2 := by
    have scaled := mul_le_mul_of_nonneg_right (show 1 ≤ Real.exp span + 1 by linarith [Real.exp_pos span]) budgetNonnegative
    simpa only [one_mul, budgetIdentity] using scaled
  have preTransport : Real.exp span * (2 * preBudget) ≤ precision / 2 := by
    have scaled := mul_le_mul_of_nonneg_right (show Real.exp span ≤ Real.exp span + 1 by linarith) budgetNonnegative
    simpa only [budgetIdentity] using scaled
  refine ⟨lift, liftProperties, liftPolar, ?_⟩
  intro time inside receiver below
  have forcingBound : multiplier / changed.location (index.val + 1) ^ 4 * (∫ current in (0 : ℝ)..time,
      Real.exp (rate * (time - current)) * forcing current) ≤ precision := by
    by_cases before : time ≤ hit
    · exact (preBound time ⟨inside.1, before⟩).trans (prePlain.trans (by linarith only [precisionPositive]))
    · have after : hit < time := lt_of_not_ge before
      have split := EulerNonuniqueness.General.exponential_convolution_split (function := forcing) (rate := rate)
        hitInside.1 after.le (history time inside).1
      rw [split.2.2.2, mul_add]
      have factorBound : Real.exp (rate * (time - hit)) ≤ Real.exp span := Real.exp_le_exp.mpr
        ((mul_le_mul_of_nonneg_right rateOmega (sub_nonneg.mpr after.le)).trans
          ((mul_le_mul_of_nonneg_left (sub_le_sub_right inside.2 hit) omegaPositive.le).trans shortSpan))
      have preScaled := mul_le_mul_of_nonneg_left (preBound hit ⟨hitInside.1, le_rfl⟩) (Real.exp_pos (rate * (time - hit))).le
      have transported := preScaled.trans ((mul_le_mul_of_nonneg_right factorBound budgetNonnegative).trans preTransport)
      have post := postBound time inside after
      have combined := add_le_add transported post
      convert combined using 1 <;> ring
  have normalized : envelope time / changed.location (index.val + 1) ^ 4 ≤ precision := by
    have actual := (history time inside).2
    change envelope time ≤ multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) * forcing current at actual
    have divided := div_le_div_of_nonneg_right actual (pow_nonneg (changed.location_pos (index.val + 1)).le 4)
    apply divided.trans
    convert forcingBound using 1
    ring
  have fullNonnegative : 0 ≤ prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch := by
    have := changed.location_pos (receiver.val + 1)
    have := changed.length_pos (receiver.val + 1)
    dsimp only [CascadeSourcePreparedPair.finiteCoordinateSize, CascadeSourcePreparedPair.rawSourceShapeBudget]
    positivity
  have component := norm_le_pi_norm (fun current : Fin count => if current.val < index.val then
    changed.location (current.val + 1) ^ 4 * (prepared.finiteCoordinateSize graph coordinate (lift current) current time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time current patch) else 0) receiver
  have scaledNonnegative := mul_nonneg (pow_nonneg (changed.location_pos (receiver.val + 1)).le 4) fullNonnegative
  simp only [below, ite_true, Real.norm_eq_abs, abs_of_nonneg scaledNonnegative] at component
  have locationOrder : changed.location (index.val + 1) ≤ changed.location (receiver.val + 1) := by
    rw [changed.location_eq_inv_pow, changed.location_eq_inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
  have scaledOrder := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (changed.location_pos _).le locationOrder 4) fullNonnegative
  have bound := scaledOrder.trans component
  have divided : prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch ≤
        envelope time / changed.location (index.val + 1) ^ 4 :=
    (le_div_iff₀ (pow_pos (changed.location_pos (index.val + 1)) 4)).mpr (by
      calc
        _ = changed.location (index.val + 1) ^ 4 *
            (prepared.finiteCoordinateSize graph coordinate (lift receiver) receiver time +
              ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver patch) := mul_comm _ _
        _ ≤ envelope time := bound)
  exact divided.trans normalized

end EulerNonuniqueness.Paper
