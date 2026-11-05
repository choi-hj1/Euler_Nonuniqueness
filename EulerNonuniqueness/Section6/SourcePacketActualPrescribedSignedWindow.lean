import EulerNonuniqueness.Section6.SourcePacketActualAdjacentSignedWindow
import EulerNonuniqueness.Section6.SourcePacketPrescribedAlignment

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem weighted_window_translation (input : ℝ → ℝ) (rate start horizon : ℝ) :
    (∫ time in start..start + horizon, Real.exp (-rate * time) * input time) =
      Real.exp (-rate * start) *
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-rate * elapsed) * input (start + elapsed) := by
  have shift := intervalIntegral.integral_comp_add_left
    (f := fun time => Real.exp (-rate * time) * input time) (a := 0) (b := horizon) start
  rw [add_zero] at shift
  rw [← shift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [show -rate * (start + elapsed) = -rate * start + -rate * elapsed by ring, Real.exp_add]
  ring

theorem exists_actual_prescribed_adjacent_signed_source_window :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 →
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    max 2 (16384 / tolerance) ≤ scales.ratio →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon initialDistance outgoingPhase : ℝ,
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    96 * initialDistance ≤ scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ (min tolerance 1) / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstDipoleCenter motion start source - secondDipoleCenter motion start source)).re →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤
      (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, motion.domain time source patch ⊆
      Metric.closedBall (quadrupoleCenter motion time source) (radiusFactor * length)) →
    ∀ timingConstant phaseTolerance angleError : ℝ,
    0 ≤ timingConstant → 0 ≤ phaseTolerance → 0 ≤ angleError →
    |start - changed.predictedTime sectionTime count (source.val + 1)| ≤
      timingConstant * phaseTolerance / changed.omega (source.val + 1) →
    (∃ winding : ℤ,
      |dipoleAngle (source.val + 1) - outgoingPhase - (winding : ℝ) * Real.pi| ≤ angleError) →
    let decay := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let delta := 2 * timingConstant * phaseTolerance / changed.ratio + 2 * angleError
    let input := fun time => (relativeBlockSourceShapeInput changed motion
      prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver source time).1
    let lower := ((7 / 8 : ℝ) - delta ^ 2 / 2 - 2 * tolerance -
      17 * Real.exp (-(3 * decay / 4) * horizon)) * seed
    ContinuousOn input (Icc 0 path.stop) ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * input (start + elapsed)) volume 0 horizon ∧
    ∃ coefficient : ℝ,
      ((7 / 8 : ℝ) - delta ^ 2 / 2) * seed ≤ coefficient ∧
      coefficient ≤ (9 / 8 : ℝ) * seed ∧
      lower ≤ ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed) ∧
      (∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time) +
        Real.exp (-decay * start) * lower ≤
        ∫ time in (0 : ℝ)..start + horizon, Real.exp (-decay * time) * input time := by
  obtain ⟨radius, radiusPositive, radiusEighth, factory⟩ := exists_actual_adjacent_signed_source_window
  refine ⟨radius, radiusPositive, radiusEighth, ?_⟩
  intro tolerance tolerancePositive toleranceOne scales amplitudePositive alphaPositive ratioLarge
    referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans radiusEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [factory tolerance tolerancePositive toleranceOne scales amplitudePositive alphaPositive ratioLarge
      referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
      radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency estimate sourceContinuous frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded timingConstant phaseTolerance angleError
    timingNonnegative phaseNonnegative angleNonnegative timingClose angleClose
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let decay := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let delta := 2 * timingConstant * phaseTolerance / changed.ratio + 2 * angleError
  let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
  let residual := 4 * Complex.arg ((changed.location (receiver.val + 1) : ℂ) -
      (changed.location (source.val + 1) : ℂ)) -
    2 * (phase (receiver.val + 1) - changed.omega (receiver.val + 1) * start) -
    2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let lower := ((7 / 8 : ℝ) - delta ^ 2 / 2 - 2 * tolerance -
    17 * Real.exp (-(3 * decay / 4) * horizon)) * seed
  obtain ⟨_, windowIntegrable, coefficient, coefficientError, coefficientUpper, windowError⟩ :=
    estimate count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
      startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
      firstInitial secondInitial initialProjection initialUpper prefixBounded
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have deltaNonnegative : 0 ≤ delta := by
    dsimp only [delta]
    exact add_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) timingNonnegative) phaseNonnegative)
      ratioPositive.le) (mul_nonneg (by norm_num) angleNonnegative)
  have nonterminal : receiver.val + 1 < count := by rw [adjacent]; exact source.isLt
  obtain ⟨winding, alignment⟩ := prescribed.adjacent_packet_alignment_modulo_source_time_bound
    frequencyPositive ratioPositive (receiver.val + 1) (by omega) nonterminal
    start outgoingPhase timingConstant phaseTolerance angleError
    (by simpa only [adjacent] using timingClose) (by simpa only [adjacent] using angleClose)
  have residualBound : |residual - (winding : ℝ) * (2 * Real.pi)| ≤ delta := by
    simpa only [residual, delta, adjacent] using alignment
  have cosineLower := cos_lower_of_wrapped_phase_bound winding deltaNonnegative residualBound
  have seedNonnegative : 0 ≤ seed := by dsimp only [seed, Scales.seed]; positivity
  have scaledCosine := mul_le_mul_of_nonneg_left cosineLower seedNonnegative
  have coefficientLower : ((7 / 8 : ℝ) - delta ^ 2 / 2) * seed ≤ coefficient := by
    have lowerError := (abs_le.mp coefficientError).1
    change -(seed / 8) ≤ coefficient - seed * Real.cos residual at lowerError
    nlinarith only [scaledCosine, lowerError]
  have windowLower : lower ≤ ∫ elapsed in (0 : ℝ)..horizon,
      Real.exp (-decay * elapsed) * input (start + elapsed) := by
    have lowerError := (abs_le.mp windowError).1
    change -(2 * tolerance * seed + 17 * seed * Real.exp (-(3 * decay / 4) * horizon)) ≤
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed)) - coefficient at lowerError
    dsimp only [lower]
    nlinarith only [lowerError, coefficientLower]
  have different : receiver ≠ source := by intro identity; have same := congrArg Fin.val identity; omega
  have inputC0 : ContinuousOn input (Icc 0 path.stop) := by
    have actual := (sourceContinuous count phase dipoleAngle prepared path receiver source different).fst
    rw [prepared.referenceIdentity] at actual
    exact actual
  have weightedC0 : ContinuousOn (fun time => Real.exp (-decay * time) * input time) (Icc 0 path.stop) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul inputC0
  have endNonnegative : 0 ≤ start + horizon := add_nonneg startNonnegative horizonNonnegative
  have originalIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 (start + horizon) :=
    (weightedC0.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc endNonnegative
  have startBound : start ≤ path.stop := by linarith only [endBound, horizonNonnegative]
  have prefixIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 start :=
    (weightedC0.mono (Icc_subset_Icc le_rfl startBound)).intervalIntegrable_of_Icc startNonnegative
  have physicalWindowIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time)
      volume start (start + horizon) :=
    (weightedC0.mono (Icc_subset_Icc startNonnegative endBound)).intervalIntegrable_of_Icc (by linarith only [horizonNonnegative])
  refine ⟨inputC0, originalIntegrable, windowIntegrable, coefficient, coefficientLower, coefficientUpper, windowLower, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left windowLower (Real.exp_pos (-decay * start)).le
  have added := add_le_add_left scaled (∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time)
  apply added.trans_eq
  rw [← weighted_window_translation input decay start horizon]
  exact intervalIntegral.integral_add_adjacent_intervals prefixIntegrable physicalWindowIntegrable

end EulerNonuniqueness.Paper

