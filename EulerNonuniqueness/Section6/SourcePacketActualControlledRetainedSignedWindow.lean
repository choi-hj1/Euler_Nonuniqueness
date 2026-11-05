import EulerNonuniqueness.Section6.CascadeActualExtentPrefixSmall
import EulerNonuniqueness.Section6.SourcePacketActualRetainedSignedWindow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem exists_uniform_actual_controlled_retained_signed_window :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient → coefficient ≤ 1 →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ tolerance : ℝ, 0 < tolerance → ∀ initialError : ℝ, initialError ≤ 1 / 64 →
    let windowTolerance := min (tolerance / 2) (1 / 8)
    ∃ ratioMin ≥ (2 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 → ratioMin ≤ scales.ratio →
    0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
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
    (∀ time ∈ Icc 0 (entry drive), ∀ patch,
      motion.domain time drive patch ⊆ Metric.closedBall (quadrupoleCenter motion time drive)
        (extent * changed.length (drive.val + 1))) →
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
    ∀ outgoingPhase : ℝ,
    2048 ≤ initialDistance drive → initialDistance drive ≤ changed.omega (drive.val + 1) / 16 →
    12 * initialDistance drive ≤ (windowTolerance / 2) * changed.ratio →
    20 * initialError + 83200 / (initialDistance drive) ^ 2 ≤ (min (windowTolerance / 4) 1) / 5120 →
    let length := changed.length (drive.val + 1)
    let outgoingDirection := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion (entry drive) drive - (length : ℂ) * outgoingDirection‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion (entry drive) drive - (length : ℂ) * (-outgoingDirection)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance drive ≤
      (Complex.I * star outgoingDirection * (firstDipoleCenter motion (entry drive) drive -
        secondDipoleCenter motion (entry drive) drive)).re →
    ‖firstDipoleCenter motion (entry drive) drive - secondDipoleCenter motion (entry drive) drive‖ ≤
      (5 / 4 : ℝ) * length * initialDistance drive →
    let omega := changed.omega (receiver.val + 1)
    let lambda := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (receiver.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (drive.val + 1) : ℂ)
    let residual := 4 * Complex.arg frozen - 2 * (phase (receiver.val + 1) - omega * entry drive) -
      2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let input := fun time => (relativeBlockSourceShapeInput changed motion prepared.reference receiver drive time).1
    ContinuousOn input (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-lambda * time) * input time) volume 0 (entry drive) ∧
    ∀ horizon : ℝ, 0 ≤ horizon → entry drive + horizon ≤ path.stop →
      IntervalIntegrable (fun time => Real.exp (-lambda * time) * input time) volume 0 (entry drive + horizon) ∧
      |Real.exp (lambda * entry drive) *
        (∫ time in (0 : ℝ)..entry drive + horizon, Real.exp (-lambda * time) * input time) / seed - Real.cos residual| ≤
          tolerance + 17 * Real.exp (-(3 * lambda / 4) * horizon) ∧
      Real.cos residual - tolerance - 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤
        Real.exp (lambda * entry drive) *
          (∫ time in (0 : ℝ)..entry drive + horizon, Real.exp (-lambda * time) * input time) / seed := by
  obtain ⟨prefixThreshold, prefixThresholdPositive, prefixThresholdEighth, rawCap, rawPositive, prefixFactories⟩ :=
    exists_uniform_actual_adjacent_extent_prefix_small
  obtain ⟨windowRadius, windowRadiusPositive, _, windowFactories⟩ := exists_actual_retained_signed_window
  let thresholdMax := min prefixThreshold windowRadius
  have thresholdPositive : 0 < thresholdMax := lt_min prefixThresholdPositive windowRadiusPositive
  have thresholdPrefix : thresholdMax ≤ prefixThreshold := min_le_left _ _
  have thresholdWindow : thresholdMax ≤ windowRadius := min_le_right _ _
  refine ⟨thresholdMax, thresholdPositive, thresholdPrefix.trans prefixThresholdEighth, rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, prefixes⟩ := prefixFactories factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro extent extentOne coefficient coefficientPositive coefficientOne magnitudeMax distanceMax magnitudeNonnegative
    distanceNonnegative tolerance tolerancePositive initialError initialErrorSmall
  let windowTolerance := min (tolerance / 2) (1 / 8)
  have windowPositive : 0 < windowTolerance := lt_min (by positivity) (by norm_num)
  have windowEighth : windowTolerance ≤ 1 / 8 := min_le_right _ _
  have windowHalf : windowTolerance ≤ tolerance / 2 := min_le_left _ _
  have prefixPositive : 0 < tolerance / 2 := by positivity
  obtain ⟨prefixRatio, prefixTwo, prefixEstimates⟩ := prefixes extent extentOne coefficient coefficientPositive coefficientOne
    magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative (tolerance / 2) prefixPositive
  let ratioMin := max prefixRatio (max 2 (65536 / windowTolerance))
  have ratioTwo : 2 ≤ ratioMin := prefixTwo.trans (le_max_left _ _)
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower timingError
    timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime boundaryConstant boundaryOne
  have prefixRatioBound : prefixRatio ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have windowRatioBound : max 2 (65536 / windowTolerance) ≤ scales.ratio := (le_max_right _ _).trans ratioLarge
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  have rootOne : 1 ≤ scaleRoot := (by norm_num : (1 : ℝ) ≤ 8).trans (rootEight.trans rootLarge)
  have amplitudePositive : 0 < scales.amplitude := by rw [amplitudeIdentity]; positivity
  filter_upwards [prefixEstimates scales scaleRoot rootLarge amplitudeIdentity prefixRatioBound alphaPositive alphaSmall
      ratioPower timingError timingErrorNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude
      threshold (thresholdBound.trans thresholdPrefix) orbit sectionTime boundaryConstant boundaryOne,
    windowFactories windowTolerance windowPositive windowEighth scales amplitudePositive alphaPositive windowRatioBound
      referenceConstant referenceNonnegative referenceAmplitude threshold (thresholdBound.trans thresholdWindow)
      orbit sectionTime factor scaleRoot boundaryConstant extent initialError factorPositive (factorSmall.trans (by norm_num))
      rootOne boundaryOne (zero_lt_one.trans_le extentOne) initialErrorSmall,
    eventually_ge_atTop (1 : ℝ)] with frequency prefixEstimate windowEstimate frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound
  dsimp only
  intro driveTiming sourceTiming entries extents domains driveReferenceExtent driveAlternativeExtent driveDomains magnitudeBounds
    distanceBounds profiles driverProfile small outgoingPhase initialLarge initialSmall ratioBudget numericBudget
  intro firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (receiver.val + 1)
  let lambda := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (receiver.val + 1)
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (drive.val + 1) : ℂ)
  let residual := 4 * Complex.arg frozen - 2 * (phase (receiver.val + 1) - omega * entry drive) -
    2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let fullInput := relativeBlockSourceShapeInput changed motion prepared.reference receiver drive
  let input := fun time => (fullInput time).1
  let prefixIntegral := ∫ time in (0 : ℝ)..entry drive, Real.exp (-lambda * time) * input time
  have prefixData := prefixEstimate count phase dipoleAngle prepared path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound driveTiming sourceTiming
    entries extents domains driveReferenceExtent driveAlternativeExtent magnitudeBounds distanceBounds profiles driverProfile small
  obtain ⟨_, prefixNormIntegrable, prefixBound⟩ := prefixData
  have windowData := windowEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver drive adjacent
    (entry drive) ⟨entryNonnegative, entryBound⟩ (initialDistance drive) outgoingPhase initialLarge initialSmall ratioBudget
    numericBudget firstInitial secondInitial initialProjection initialUpper driveDomains
  dsimp only at windowData
  simp only [← prepared.referenceIdentity] at windowData
  obtain ⟨inputContinuous, _, _, prefixIntegrable, _, _, _, windows⟩ := windowData
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have scalarAbsoluteIntegrable : IntervalIntegrable (fun time => |Real.exp (-lambda * time) * input time|)
      volume 0 (entry drive) := by simpa only [Real.norm_eq_abs] using prefixIntegrable.norm
  have prefixProjection : |prefixIntegral| ≤ ∫ time in (0 : ℝ)..entry drive,
      Real.exp (-lambda * time) * ‖fullInput time‖ := by
    apply (intervalIntegral.abs_integral_le_integral_abs entryNonnegative).trans
    apply intervalIntegral.integral_mono_on entryNonnegative scalarAbsoluteIntegrable prefixNormIntegrable
    intro time _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using norm_fst_le (fullInput time)) (Real.exp_pos _).le
  have normalizedPrefix : Real.exp (lambda * entry drive) * |prefixIntegral| / seed ≤ tolerance / 2 := by
    apply (div_le_iff₀ seedPositive).mpr
    exact (mul_le_mul_of_nonneg_left prefixProjection (Real.exp_pos _).le).trans prefixBound
  refine ⟨inputContinuous, prefixIntegrable, ?_⟩
  intro horizon horizonNonnegative endBound
  obtain ⟨originalIntegrable, _, _, _, estimate⟩ := windows horizon horizonNonnegative endBound
  have normalizedBound : |Real.exp (lambda * entry drive) *
      (∫ time in (0 : ℝ)..entry drive + horizon, Real.exp (-lambda * time) * input time) / seed - Real.cos residual| ≤
        tolerance + 17 * Real.exp (-(3 * lambda / 4) * horizon) := by
    change |Real.exp (lambda * entry drive) *
      (∫ time in (0 : ℝ)..entry drive + horizon, Real.exp (-lambda * time) * input time) / seed - Real.cos residual| ≤
        windowTolerance + Real.exp (lambda * entry drive) * |prefixIntegral| / seed +
          17 * Real.exp (-(3 * lambda / 4) * horizon) at estimate
    linarith only [estimate, normalizedPrefix, windowHalf]
  refine ⟨originalIntegrable, normalizedBound, ?_⟩
  have lower := (abs_le.mp normalizedBound).1
  linarith only [lower]

end EulerNonuniqueness.Paper
