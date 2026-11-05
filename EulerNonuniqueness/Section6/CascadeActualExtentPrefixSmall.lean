import EulerNonuniqueness.Section5.CascadeAdjacentReceiverPrefixTranslationSmall
import EulerNonuniqueness.Section6.CascadeActualExtentPrefix
import EulerNonuniqueness.General.ReciprocalPolynomialSmallness

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem adjacent_motion_strength_seed_identity (scales : Scales) (index : ℕ)
    (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio) :
    (scales.circulation (index + 1) * scales.length (index + 1) ^ 2 /
      |scales.location index - scales.location (index + 1)| ^ 5) * scales.location index =
      (2 * Real.sqrt 2 * Real.pi / Real.sqrt 3) * (scales.omega index / scales.ratio) * scales.seed index := by
  have omegaPositive := scales.omega_pos frequencyPositive ratioPositive index
  have locationPositive := scales.location_pos (index + 1)
  have omegaNext : scales.omega (index + 1) = scales.omega index * scales.ratio := by
    simp only [Scales.omega, pow_succ]; ring
  have locationDouble : scales.location index = 2 * scales.location (index + 1) := by
    simp only [scales.location_eq_half_pow, pow_succ]; ring
  simp only [Scales.seed, scales.adjacent_location_distance, Scales.circulation, omegaNext]
  rw [locationDouble]
  field_simp [omegaPositive.ne', ratioPositive.ne', locationPositive.ne', Real.pi_ne_zero,
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne',
    (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne']
  ring

theorem exists_uniform_actual_adjacent_extent_prefix_small :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient → coefficient ≤ 1 →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ tolerance : ℝ, 0 < tolerance → ∃ ratioMin ≥ (2 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    ratioMin ≤ scales.ratio → 0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ timingError : ℝ, 0 ≤ timingError →
    (coefficient * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ),
    1 ≤ boundaryConstant → ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver drive : Fin count, receiver.val + 1 = drive.val → drive.val + 1 < count →
    ∀ entry initialDistance magnitude : Fin count → ℝ, ∀ direction : Fin count → ℂ, ∀ actualTime : ℕ → ℝ,
    (∀ source : Fin count, actualTime (source.val + 1) = entry source) →
    0 ≤ entry drive → entry drive ≤ path.stop →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    |actualTime (drive.val + 1) - changed.predictedTime sectionTime count (drive.val + 1)| ≤
      timingError / changed.omega (drive.val + 1) →
    (∀ source : Fin count, drive.val < source.val →
      |actualTime (source.val + 1) - changed.predictedTime sectionTime count (source.val + 1)| ≤
        timingError / changed.omega (source.val + 1)) →
    (∀ source : Fin count, drive.val < source.val →
      let length := changed.length (source.val + 1)
      0 ≤ entry source ∧ entry source ≤ entry drive ∧ 512 ≤ initialDistance source ∧
      initialDistance source ≤ changed.omega (source.val + 1) / 16 ∧ ‖direction source‖ = 1 ∧
      ‖firstDipoleSeparation motion (entry source) source - (length : ℂ) * direction source‖ ≤ length / 64 ∧
      ‖secondDipoleSeparation motion (entry source) source - (length : ℂ) * (-direction source)‖ ≤ length / 64 ∧
      (3 / 4 : ℝ) * length * initialDistance source ≤
        (Complex.I * star (direction source) * (firstDipoleCenter motion (entry source) source -
          secondDipoleCenter motion (entry source) source)).re ∧
      ‖firstDipoleCenter motion (entry source) source - secondDipoleCenter motion (entry source) source‖ ≤
        (5 / 4 : ℝ) * length * initialDistance source) →
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source),
      (∀ patch : Fin 4, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * changed.length (source.val + 1)) ∧
      (∀ patch : Fin 4, ‖patchCentroid motion time source patch - quadrupoleCenter motion time source‖ ≤
        extent * changed.length (source.val + 1))) →
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source), ∀ patch,
      motion.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter motion time source)
        (extent * changed.length (source.val + 1))) →
    (∀ time ∈ Icc 0 (entry drive), ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time drive patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time drive‖ ≤
          extent * changed.length (drive.val + 1)) →
    (∀ time ∈ Icc 0 (entry drive), ∀ patch : Fin 4,
      ‖patchCentroid motion time drive patch - quadrupoleCenter motion time drive‖ ≤
        extent * changed.length (drive.val + 1)) →
    (∀ source : Fin count, drive.val < source.val → 0 ≤ magnitude source ∧ magnitude source ≤ magnitudeMax) →
    (∀ source : Fin count, drive.val < source.val → initialDistance source ≤ distanceMax) →
    let sharpState := fun (source : Fin count) time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    (∀ source : Fin count, drive.val < source.val → ∀ time ∈ Icc 0 (entry source), sharpState source time ≤
      magnitude source * Real.exp (coefficient * changed.omega (source.val + 1) * (time - entry source))) →
    (∀ time ∈ Icc 0 (entry drive), sharpState drive time ≤ magnitudeMax *
      Real.exp (coefficient * changed.omega (drive.val + 1) * (time - entry drive))) →
    (∀ current : Fin count, current.val < drive.val → ∀ time ∈ Icc 0 (entry drive),
      |unstableShape motion time current| + |stableShape motion time current| ≤ radius) →
    let lambda := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let input := relativeBlockSourceShapeInput changed motion prepared.reference receiver drive
    ContinuousOn input (Icc 0 (entry drive)) ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) * ‖input time‖) volume 0 (entry drive) ∧
    Real.exp (lambda * entry drive) *
      (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * ‖input time‖) ≤
        tolerance * changed.seed (receiver.val + 1) := by
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, receiverCap, receiverPositive, receiverFactories⟩ :=
    exists_uniform_actual_adjacent_receiver_prefix_translation_small
  obtain ⟨extentCap, extentPositive, extentConstant, extentNonnegative, extentFactories⟩ :=
    exists_uniform_actual_adjacent_extent_prefix
  let rawCap := min receiverCap extentCap
  have rawPositive : 0 < rawCap := lt_min receiverPositive extentPositive
  have receiverCapBound : rawCap ≤ receiverCap := min_le_left _ _
  have extentCapBound : rawCap ≤ extentCap := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, responseConstant, responseOne, rootMin, rootEight, receivers⟩ :=
    receiverFactories factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro extent extentOne coefficient coefficientPositive coefficientOne magnitudeMax distanceMax magnitudeNonnegative
    distanceNonnegative tolerance tolerancePositive
  let normalization := 2 * Real.sqrt 2 * Real.pi / Real.sqrt 3
  have normalizationNonnegative : 0 ≤ normalization := by dsimp only [normalization]; positivity
  let motionConstant := extentConstant * extent ^ 2 * normalization
  have motionNonnegative : 0 ≤ motionConstant := mul_nonneg (mul_nonneg extentNonnegative (sq_nonneg extent)) normalizationNonnegative
  let translationTolerance := tolerance / (2 * (1 + motionConstant))
  have translationPositive : 0 < translationTolerance := by dsimp only [translationTolerance]; positivity
  have quadraticNonnegative : 0 ≤ 100 * extentConstant * extent ^ 2 * magnitudeMax / coefficient := by positivity
  obtain ⟨incomingRatio, incomingTwo, incomingEstimates⟩ := General.exists_uniform_reciprocal_quadratic_small
    (linear := 0) quadraticNonnegative (show 0 < tolerance / 2 by positivity)
  let receiverRatio := max (max 2 (2 * responseConstant))
    (max (4 * responseConstant / coefficient) (4 * Real.sqrt 2 / coefficient))
  let ratioMin := max receiverRatio incomingRatio
  have ratioTwo : 2 ≤ ratioMin := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower timingError
    timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime boundaryConstant boundaryOne
  have receiverRatioBound : receiverRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have incomingSmall : 100 * extentConstant * extent ^ 2 * magnitudeMax / (coefficient * scales.ratio ^ 2) ≤ tolerance / 2 := by
    simpa only [zero_div, add_zero, div_div] using incomingEstimates scales.ratio ((le_max_right _ _).trans ratioLarge)
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  filter_upwards [receivers extent extentOne coefficient coefficientPositive coefficientOne magnitudeMax distanceMax
      magnitudeNonnegative distanceNonnegative translationTolerance translationPositive scales scaleRoot rootLarge amplitudeIdentity
      receiverRatioBound alphaPositive alphaSmall ratioPower timingError timingErrorNonnegative ratioSeparation
      referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime boundaryConstant boundaryOne,
    extentFactories extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    eventually_ge_atTop (1 : ℝ)] with frequency receiverEstimate extentEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound
  dsimp only
  intro driveTiming sourceTiming entries extents domains driveReferenceExtent driveAlternativeExtent magnitudeBounds
    distanceBounds profiles driverProfile small
  let changed : Scales := {scales with frequency := frequency}
  let receiverIndex := receiver.val + 1
  let motion := prepared.trajectory.movingFamily.patchMotion
  let lambda := 2 * Real.sqrt 2 * changed.omega receiverIndex
  let nu := coefficient * changed.omega (drive.val + 1)
  let gap := |changed.location receiverIndex - changed.location (drive.val + 1)|
  let strength := changed.circulation (drive.val + 1) * changed.length (drive.val + 1) ^ 2 / gap ^ 5
  let input := relativeBlockSourceShapeInput changed motion prepared.reference receiver drive
  let translation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ /
    changed.location receiverIndex
  have rawCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have centeredCapInvariant {largerCap : ℝ} (bound : rawCap ≤ largerCap) :
      (prepared.enlargeCap bound).rawSourceCenteredState = prepared.rawSourceCenteredState := rfl
  have receiverData := receiverEstimate count phase dipoleAngle (prepared.enlargeCap receiverCapBound) path receiver drive
    adjacent driveNonterminal entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound
  dsimp only at receiverData
  simp only [rawCapInvariant, centeredCapInvariant] at receiverData
  have receiverActual := receiverData driveTiming sourceTiming entries extents domains magnitudeBounds distanceBounds profiles driverProfile small
  have receiverBound : (changed.omega receiverIndex / changed.ratio) * Real.exp (lambda * entry drive) *
      (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time) ≤ translationTolerance := receiverActual.2.2
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive receiverIndex
  have locationPositive := changed.location_pos receiverIndex
  have seedNonnegative := (changed.seed_pos frequencyPositive ratioPositive receiverIndex).le
  have driveIndex : drive.val + 1 = receiverIndex + 1 := by dsimp only [receiverIndex]; omega
  have omegaDrive : changed.omega (drive.val + 1) = changed.omega receiverIndex * changed.ratio := by
    rw [driveIndex]; simp only [Scales.omega, pow_succ]; ring
  have rateSeparated : lambda ≤ nu / 2 := by
    have ratioLambda : 4 * Real.sqrt 2 / coefficient ≤ changed.ratio :=
      (le_max_right _ _).trans ((le_max_right _ _).trans receiverRatioBound)
    have scaled := (div_le_iff₀ coefficientPositive).mp ratioLambda
    dsimp only [lambda, nu]
    rw [omegaDrive]
    nlinarith only [mul_le_mul_of_nonneg_right scaled omegaPositive.le]
  have extentData := extentEstimate count phase dipoleAngle (prepared.enlargeCap extentCapBound) path receiver drive adjacent
    (entry drive) coefficient magnitudeMax entryNonnegative entryBound coefficientPositive magnitudeNonnegative
    driveReferenceExtent driveAlternativeExtent
  dsimp only at extentData
  simp only [rawCapInvariant, centeredCapInvariant] at extentData
  obtain ⟨inputContinuous, _, prefixBounds⟩ := extentData rateSeparated driverProfile
  obtain ⟨inputIntegrable, _, prefixBound⟩ := prefixBounds (entry drive) ⟨entryNonnegative, le_rfl⟩
  change (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * ‖input time‖) ≤
    (100 * (extentConstant * extent ^ 2) / coefficient) * magnitudeMax *
      (changed.seed receiverIndex / changed.ratio ^ 2) * Real.exp (-lambda * entry drive) *
        Real.exp ((nu - lambda) * (entry drive - entry drive)) +
    (extentConstant * extent ^ 2) * strength * ∫ time in (0 : ℝ)..entry drive,
      Real.exp (-lambda * time) * ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ at prefixBound
  simp only [sub_self, mul_zero, Real.exp_zero, mul_one] at prefixBound
  have receiverIntegral : (∫ time in (0 : ℝ)..entry drive,
      Real.exp (-lambda * time) * ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖) =
      changed.location receiverIndex * ∫ time in (0 : ℝ)..entry drive,
        Real.exp (-lambda * time) * translation time := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro time _
    dsimp only [translation]
    field_simp [locationPositive.ne']
  rw [receiverIntegral] at prefixBound
  have strengthSeed : strength * changed.location receiverIndex =
      normalization * (changed.omega receiverIndex / changed.ratio) * changed.seed receiverIndex := by
    simpa only [strength, gap, driveIndex, normalization] using
      adjacent_motion_strength_seed_identity changed receiverIndex frequencyPositive ratioPositive
  have exponentialCancellation : Real.exp (lambda * entry drive) * Real.exp (-lambda * entry drive) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  let receiverAction := (changed.omega receiverIndex / changed.ratio) * Real.exp (lambda * entry drive) *
    ∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time
  have budgetIdentity : Real.exp (lambda * entry drive) *
      ((100 * (extentConstant * extent ^ 2) / coefficient) * magnitudeMax *
        (changed.seed receiverIndex / changed.ratio ^ 2) * Real.exp (-lambda * entry drive) +
      (extentConstant * extent ^ 2) * strength * (changed.location receiverIndex *
        ∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time)) =
      (100 * extentConstant * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2) +
        motionConstant * receiverAction) * changed.seed receiverIndex := by
    calc
      _ = (100 * extentConstant * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2)) *
          (Real.exp (lambda * entry drive) * Real.exp (-lambda * entry drive)) * changed.seed receiverIndex +
        (extentConstant * extent ^ 2) * (strength * changed.location receiverIndex) * Real.exp (lambda * entry drive) *
          (∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * translation time) := by
            simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [exponentialCancellation, strengthSeed]; dsimp only [motionConstant, receiverAction]; ring
  have motionTolerance : motionConstant * translationTolerance ≤ tolerance / 2 := by
    have quotient := (div_le_one (show 0 < 1 + motionConstant by positivity)).mpr (by linarith : motionConstant ≤ 1 + motionConstant)
    have scaled := mul_le_mul_of_nonneg_left quotient (show 0 ≤ tolerance / 2 by positivity)
    calc
      _ = (tolerance / 2) * (motionConstant / (1 + motionConstant)) := by
        dsimp only [translationTolerance]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ring
      _ ≤ _ := by simpa only [mul_one] using scaled
  have motionBound : motionConstant * receiverAction ≤ tolerance / 2 :=
    (mul_le_mul_of_nonneg_left receiverBound motionNonnegative).trans motionTolerance
  have coefficientBound : 100 * extentConstant * extent ^ 2 * magnitudeMax / (coefficient * changed.ratio ^ 2) +
      motionConstant * receiverAction ≤ tolerance := by linarith only [incomingSmall, motionBound]
  have scaled := mul_le_mul_of_nonneg_left prefixBound (Real.exp_pos (lambda * entry drive)).le
  rw [budgetIdentity] at scaled
  refine ⟨inputContinuous, inputIntegrable, ?_⟩
  exact scaled.trans (mul_le_mul_of_nonneg_right coefficientBound seedNonnegative)

end EulerNonuniqueness.Paper
