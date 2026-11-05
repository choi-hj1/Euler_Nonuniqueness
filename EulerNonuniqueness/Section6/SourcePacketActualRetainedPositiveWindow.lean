import EulerNonuniqueness.Section6.SourcePacketActualControlledRetainedSignedWindow
import EulerNonuniqueness.Section5.CascadeAdjacentSourcePhase

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace EulerNonuniqueness.Paper
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

theorem exists_uniform_actual_controlled_retained_positive_window :
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧ ∃ rawCap > (0 : ℝ),
    ∀ factor : ℝ, 0 < factor → factor ≤ 1 / 100 →
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧ ∃ rootMin ≥ (8 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent → ∀ coefficient : ℝ, 0 < coefficient → coefficient ≤ 1 →
    ∀ magnitudeMax distanceMax : ℝ, 0 ≤ magnitudeMax → 0 ≤ distanceMax →
    ∀ initialError : ℝ, initialError ≤ 1 / 64 →
    ∀ phaseTolerance : ℝ, 0 ≤ phaseTolerance →
    let windowTolerance := (1 / 32 : ℝ)
    ∃ ratioMin ≥ (2 : ℝ), ∀ (scales : Scales) (scaleRoot : ℝ),
    rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 → ratioMin ≤ scales.ratio →
    0 < scales.alpha → scales.alpha < 1 → 4 < scales.ratio ^ scales.alpha →
    ∀ timingError : ℝ, 0 ≤ timingError →
    3 * timingError + 2 * phaseTolerance ≤ 1 / 2 →
    (coefficient * scales.ratio + 1) * 8 ≤
      scales.ratio ^ scales.alpha * (scales.ratio ^ (1 - scales.alpha) - 1) →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude →
    ∀ threshold ≤ thresholdMax, ∀ (orbit : SeparatingOrbit) (sectionTime boundaryConstant : ℝ),
    1 ≤ boundaryConstant → ∀ᶠ frequency : ℝ in atTop,
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
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
    ∀ outgoingPhase : ℝ, ∀ sourceWinding : ℤ,
    let timingShift := changed.omega (drive.val + 1) *
      (entry drive - changed.predictedTime sectionTime count (drive.val + 1))
    let phaseError := outgoingPhase - dipoleAngle (drive.val + 1) + timingShift - (sourceWinding : ℝ) * Real.pi
    |phaseError| ≤ phaseTolerance →
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
    (7 / 8 : ℝ) ≤ Real.cos residual ∧
    ∀ horizon : ℝ, 0 ≤ horizon → entry drive + horizon ≤ path.stop → 512 ≤ lambda * horizon →
      IntervalIntegrable (fun time => Real.exp (-lambda * time) * input time) volume 0 (entry drive + horizon) ∧
      (3 / 4 : ℝ) ≤ Real.exp (lambda * entry drive) *
        (∫ time in (0 : ℝ)..entry drive + horizon, Real.exp (-lambda * time) * input time) / seed := by
  classical
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, factors⟩ :=
    exists_uniform_actual_controlled_retained_signed_window
  refine ⟨thresholdMax, thresholdPositive, thresholdEighth, rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, parameters⟩ := factors factor factorPositive factorSmall
  refine ⟨radius, radiusPositive, radiusQuarter, rootMin, rootEight, ?_⟩
  intro extent extentOne coefficient coefficientPositive coefficientOne magnitudeMax distanceMax magnitudeNonnegative
    distanceNonnegative initialError initialErrorSmall phaseTolerance phaseNonnegative
  dsimp only
  obtain ⟨ratioMin, ratioTwo, scalesFactory⟩ := parameters extent extentOne coefficient coefficientPositive coefficientOne
    magnitudeMax distanceMax magnitudeNonnegative distanceNonnegative (1 / 16) (by norm_num) initialError initialErrorSmall
  refine ⟨ratioMin, ratioTwo, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower timingError
    timingNonnegative phaseBudget ratioSeparation referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
    orbit sectionTime boundaryConstant boundaryOne
  have ratioBound : 2 ≤ scales.ratio := ratioTwo.trans ratioLarge
  filter_upwards [scalesFactory scales scaleRoot rootLarge amplitudeIdentity ratioLarge alphaPositive alphaSmall ratioPower
      timingError timingNonnegative ratioSeparation referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound
      orbit sectionTime boundaryConstant boundaryOne,
    eventually_gt_atTop (0 : ℝ)] with frequency window frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared prescribed path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound
  intro driveTiming sourceTiming entries extents domains driveReferenceExtent driveAlternativeExtent driveDomains magnitudeBounds
    distanceBounds profiles driverProfile small outgoingPhase sourceWinding phaseSmall initialLarge initialSmall ratioBudget numericBudget
    firstInitial secondInitial initialProjection initialUpper
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let omega := changed.omega (receiver.val + 1)
  let lambda := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (receiver.val + 1)
  let residual := 4 * Complex.arg ((changed.location (receiver.val + 1) : ℂ) - (changed.location (drive.val + 1) : ℂ)) -
    2 * (phase (receiver.val + 1) - omega * entry drive) - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have driveOmegaPositive := changed.omega_pos frequencyPositive ratioPositive (drive.val + 1)
  have timingSmall : |changed.omega (drive.val + 1) *
      (entry drive - changed.predictedTime sectionTime count (drive.val + 1))| ≤ timingError := by
    have actual : |entry drive - changed.predictedTime sectionTime count (drive.val + 1)| ≤
        timingError / changed.omega (drive.val + 1) := by simpa only [timeIdentity] using driveTiming
    have product := (le_div_iff₀ driveOmegaPositive).mp actual
    rw [abs_mul, abs_of_pos driveOmegaPositive]
    nlinarith only [product]
  have cosine := prescribed.adjacent_source_phase_cos_lower ratioBound receiver drive adjacent
    (entry drive) outgoingPhase timingError phaseTolerance sourceWinding timingSmall phaseSmall phaseBudget
  have windowToleranceIdentity : min ((1 / 16 : ℝ) / 2) (1 / 8) = 1 / 32 := by norm_num
  have data := window count phase dipoleAngle prepared path receiver drive adjacent driveNonterminal
    entry initialDistance magnitude direction actualTime timeIdentity entryNonnegative entryBound driveTiming sourceTiming
    entries extents domains driveReferenceExtent driveAlternativeExtent driveDomains magnitudeBounds distanceBounds profiles driverProfile small
    outgoingPhase initialLarge initialSmall (by simpa only [windowToleranceIdentity] using ratioBudget)
    (by simpa only [windowToleranceIdentity] using numericBudget) firstInitial secondInitial initialProjection initialUpper
  dsimp only at data
  obtain ⟨inputContinuous, prefixI, estimates⟩ := data
  refine ⟨inputContinuous, prefixI, cosine, ?_⟩
  intro horizon horizonNonnegative horizonBound elapsedLarge
  obtain ⟨integrable, _, lower⟩ := estimates horizon horizonNonnegative horizonBound
  have exponentLarge : (384 : ℝ) ≤ (3 * lambda / 4) * horizon := by
    change 512 ≤ lambda * horizon at elapsedLarge
    nlinarith only [elapsedLarge]
  have exponentialLarge : (385 : ℝ) ≤ Real.exp ((3 * lambda / 4) * horizon) := by
    have linear := Real.add_one_le_exp ((3 * lambda / 4) * horizon)
    linarith only [linear, exponentLarge]
  have exponentialSmall : Real.exp (-((3 * lambda / 4) * horizon)) ≤ 1 / 385 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 385) exponentialLarge
  have tail : 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤ 1 / 16 := by
    have same : -(3 * lambda / 4) * horizon = -((3 * lambda / 4) * horizon) := by ring
    rw [same]
    have scaled := mul_le_mul_of_nonneg_left exponentialSmall (by norm_num : (0 : ℝ) ≤ 17)
    norm_num at scaled ⊢
    linarith only [scaled]
  refine ⟨integrable, ?_⟩
  change Real.cos residual - (1 / 16 : ℝ) - 17 * Real.exp (-(3 * lambda / 4) * horizon) ≤ _ at lower
  change (7 / 8 : ℝ) ≤ Real.cos residual at cosine
  linarith only [lower, tail, cosine]

end EulerNonuniqueness.Paper
