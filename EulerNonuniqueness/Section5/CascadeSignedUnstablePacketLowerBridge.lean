import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel
import EulerNonuniqueness.Section5.CascadeLeadingDrivenWeightedReturn
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity
import EulerNonuniqueness.Section6.SourcePacketActualPrescribedSignedWindow

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem signed_packet_lower_of_original_history
    {trajectory leading source remainder nonadjacent remainderNorm : ℝ → ℝ}
    {rate start horizon lower bound : ℝ}
    (startNonnegative : 0 ≤ start) (horizonNonnegative : 0 ≤ horizon)
    (leadingContinuous : ContinuousOn leading (Icc 0 (start + horizon)))
    (sourceContinuous : ContinuousOn source (Icc 0 (start + horizon)))
    (remainderContinuous : ContinuousOn remainder (Icc 0 (start + horizon)))
    (nonadjacentContinuous : ContinuousOn nonadjacent (Icc 0 (start + horizon)))
    (normContinuous : ContinuousOn remainderNorm (Icc 0 (start + horizon)))
    (nonadjacentNonnegative : ∀ time, 0 ≤ nonadjacent time)
    (normNonnegative : ∀ time, 0 ≤ remainderNorm time)
    (leadingLower : ∀ time, -nonadjacent time ≤ leading time - source time)
    (remainderLower : ∀ time, -remainderNorm time ≤ remainder time)
    (history : ∀ time ∈ Icc 0 (start + horizon), Real.exp (-rate * time) * trajectory time =
      (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * leading current) +
        ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * remainder current)
    (packetLower : (∫ current in (0 : ℝ)..start, Real.exp (-rate * current) * source current) +
      Real.exp (-rate * start) * lower ≤
        ∫ current in (0 : ℝ)..start + horizon, Real.exp (-rate * current) * source current)
    (errorBound : (∫ current in (0 : ℝ)..start + horizon, Real.exp (-rate * current) * nonadjacent current) ≤ bound) :
    let action := fun function first last => ∫ current in first..last, Real.exp (-rate * current) * function current
    Real.exp (-rate * start) * trajectory start = action source 0 start + action (fun time => leading time - source time) 0 start + action remainder 0 start ∧
    action source 0 start + Real.exp (-rate * start) * lower - bound - action remainderNorm 0 (start + horizon) ≤
      Real.exp (-rate * (start + horizon)) * trajectory (start + horizon) ∧
    trajectory start + lower - Real.exp (rate * start) * (bound + action remainderNorm 0 (start + horizon)) ≤
      Real.exp (-rate * horizon) * trajectory (start + horizon) := by
  let finish := start + horizon
  let action := fun (function : ℝ → ℝ) first last => ∫ current in first..last, Real.exp (-rate * current) * function current
  have finishNonnegative : 0 ≤ finish := add_nonneg startNonnegative horizonNonnegative
  have startBound : start ≤ finish := le_add_of_nonneg_right horizonNonnegative
  have exponential : Continuous (fun current : ℝ => Real.exp (-rate * current)) := by fun_prop
  have fullI (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun current => Real.exp (-rate * current) * function current) volume 0 finish :=
    (exponential.continuousOn.mul continuous).intervalIntegrable_of_Icc finishNonnegative
  have prefixI (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun current => Real.exp (-rate * current) * function current) volume 0 start :=
    (exponential.continuousOn.mul (continuous.mono (Icc_subset_Icc le_rfl startBound))).intervalIntegrable_of_Icc startNonnegative
  have windowI (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) :
      IntervalIntegrable (fun current => Real.exp (-rate * current) * function current) volume start finish :=
    (exponential.continuousOn.mul (continuous.mono (Icc_subset_Icc startNonnegative le_rfl))).intervalIntegrable_of_Icc startBound
  have split (function : ℝ → ℝ) (continuous : ContinuousOn function (Icc 0 finish)) :
      action function 0 start + action function start finish = action function 0 finish :=
    intervalIntegral.integral_add_adjacent_intervals (prefixI function continuous) (windowI function continuous)
  have lowerIntegral (function envelope : ℝ → ℝ)
      (continuous : ContinuousOn function (Icc 0 finish)) (envelopeContinuous : ContinuousOn envelope (Icc 0 finish))
      (nonnegative : ∀ time, 0 ≤ envelope time) (lowerPoint : ∀ time, -envelope time ≤ function time)
      (first : ℝ) (firstInside : first ∈ Icc 0 finish) :
      -action envelope 0 finish ≤ action function first finish := by
    have functionI := (exponential.continuousOn.mul (continuous.mono (Icc_subset_Icc firstInside.1 le_rfl))).intervalIntegrable_of_Icc (μ := volume) firstInside.2
    have envelopeI := (exponential.continuousOn.mul (envelopeContinuous.mono (Icc_subset_Icc firstInside.1 le_rfl))).intervalIntegrable_of_Icc (μ := volume) firstInside.2
    have comparison := intervalIntegral.integral_mono_on firstInside.2 envelopeI.neg functionI (fun current _ => by
      simpa only [mul_neg] using mul_le_mul_of_nonneg_left (lowerPoint current) (Real.exp_pos _).le)
    have extension : action envelope first finish ≤ action envelope 0 finish := by
      apply intervalIntegral.integral_mono_interval firstInside.1 firstInside.2 le_rfl
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with current _
        exact mul_nonneg (Real.exp_pos _).le (nonnegative current)
      · exact fullI envelope envelopeContinuous
    change (∫ current in first..finish, -(Real.exp (-rate * current) * envelope current)) ≤
      (∫ current in first..finish, Real.exp (-rate * current) * function current) at comparison
    rw [intervalIntegral.integral_neg] at comparison
    exact (neg_le_neg extension).trans comparison
  have differenceContinuous := leadingContinuous.sub sourceContinuous
  have leadingIdentity (time : ℝ) (inside : time ∈ Icc 0 finish) :
      action leading 0 time = action source 0 time + action (fun current => leading current - source current) 0 time := by
    have localSource := (exponential.continuousOn.mul (sourceContinuous.mono (Icc_subset_Icc le_rfl inside.2))).intervalIntegrable_of_Icc (μ := volume) inside.1
    have localDifference := (exponential.continuousOn.mul (differenceContinuous.mono (Icc_subset_Icc le_rfl inside.2))).intervalIntegrable_of_Icc (μ := volume) inside.1
    rw [← intervalIntegral.integral_add localSource localDifference]
    apply intervalIntegral.integral_congr
    intro current _
    ring
  have initialIdentity := history start ⟨startNonnegative, startBound⟩
  have finalIdentity := history finish ⟨finishNonnegative, le_rfl⟩
  change Real.exp (-rate * start) * trajectory start = action leading 0 start + action remainder 0 start at initialIdentity
  change Real.exp (-rate * finish) * trajectory finish = action leading 0 finish + action remainder 0 finish at finalIdentity
  have prefixIdentity := initialIdentity.trans (by rw [leadingIdentity start ⟨startNonnegative, startBound⟩])
  have errorWhole := (neg_le_neg errorBound).trans (lowerIntegral _ _ differenceContinuous nonadjacentContinuous nonadjacentNonnegative leadingLower 0 ⟨le_rfl, finishNonnegative⟩)
  have remainderWhole := lowerIntegral _ _ remainderContinuous normContinuous normNonnegative remainderLower 0 ⟨le_rfl, finishNonnegative⟩
  have prefixBound : action source 0 start + Real.exp (-rate * start) * lower - bound - action remainderNorm 0 finish ≤
      Real.exp (-rate * finish) * trajectory finish := by
    rw [leadingIdentity finish ⟨finishNonnegative, le_rfl⟩] at finalIdentity
    linarith only [packetLower, errorWhole, remainderWhole, finalIdentity]
  have errorWindow := (neg_le_neg errorBound).trans (lowerIntegral _ _ differenceContinuous nonadjacentContinuous nonadjacentNonnegative leadingLower start ⟨startNonnegative, startBound⟩)
  have remainderWindow := lowerIntegral _ _ remainderContinuous normContinuous normNonnegative remainderLower start ⟨startNonnegative, startBound⟩
  have sourceSplit := split source sourceContinuous
  have leadingSplit := split leading leadingContinuous
  have remainderSplit := split remainder remainderContinuous
  have differenceWindow : action leading start finish = action source start finish + action (fun current => leading current - source current) start finish := by
    rw [← intervalIntegral.integral_add (windowI source sourceContinuous) (windowI _ differenceContinuous)]
    apply intervalIntegral.integral_congr
    intro current _
    ring
  have retained : Real.exp (-rate * start) * trajectory start + Real.exp (-rate * start) * lower - bound - action remainderNorm 0 finish ≤
      Real.exp (-rate * finish) * trajectory finish := by
    rw [differenceWindow] at leadingSplit
    linarith only [initialIdentity, finalIdentity, leadingSplit, remainderSplit, sourceSplit, packetLower, errorWindow, remainderWindow]
  have scaled := mul_le_mul_of_nonneg_left retained (Real.exp_pos (rate * start)).le
  have cancellation : Real.exp (rate * start) * Real.exp (-rate * start) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have shifted : Real.exp (rate * start) * Real.exp (-rate * finish) = Real.exp (-rate * horizon) := by rw [← Real.exp_add]; congr 1; dsimp only [finish]; ring
  refine ⟨prefixIdentity, prefixBound, ?_⟩
  calc
    _ = Real.exp (rate * start) * (Real.exp (-rate * start) * trajectory start + Real.exp (-rate * start) * lower - bound - action remainderNorm 0 finish) := by
      simp only [mul_sub, mul_add, ← mul_assoc, cancellation, one_mul]
      ring
    _ ≤ Real.exp (rate * start) * (Real.exp (-rate * finish) * trajectory finish) := scaled
    _ = _ := by rw [← mul_assoc, shifted]

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_signed_unstable_packet_lower_bridge
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∃ thresholdMax > (0 : ℝ), thresholdMax ≤ 1 / 8 ∧
    ∀ packetTolerance : ℝ, 0 < packetTolerance → packetTolerance ≤ 1 →
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    max 2 (16384 / packetTolerance) ≤ scales.ratio → 4 < scales.ratio ^ scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ thresholdMax,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ returnTolerance : ℝ, 0 < returnTolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    PrescribedCascadePhases {scales with frequency := frequency} orbit sectionTime count phase dipoleAngle →
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon initialDistance outgoingPhase : ℝ,
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance → initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    96 * initialDistance ≤ scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ (min packetTolerance 1) / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation first start source - (length : ℂ) * direction‖ ≤ initialError * length →
    ‖secondDipoleSeparation first start source - (length : ℂ) * (-direction)‖ ≤ initialError * length →
    (3 / 4 : ℝ) * length * initialDistance ≤ (Complex.I * star direction * (firstDipoleCenter first start source - secondDipoleCenter first start source)).re →
    ‖firstDipoleCenter first start source - secondDipoleCenter first start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    (∀ time ∈ Icc 0 start, ∀ patch, first.domain time source patch ⊆ Metric.closedBall (quadrupoleCenter first time source) (radiusFactor * length)) →
    (∀ time ∈ Icc 0 (start + horizon), |unstableShape first time receiver| + |stableShape first time receiver| ≤ radius) →
    ∀ timingConstant phaseTolerance angleError : ℝ,
    0 ≤ timingConstant → 0 ≤ phaseTolerance → 0 ≤ angleError →
    |start - changed.predictedTime sectionTime count (source.val + 1)| ≤ timingConstant * phaseTolerance / changed.omega (source.val + 1) →
    (∃ winding : ℤ, |dipoleAngle (source.val + 1) - outgoingPhase - (winding : ℝ) * Real.pi| ≤ angleError) →
    let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let delta := 2 * timingConstant * phaseTolerance / changed.ratio + 2 * angleError
    let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
    let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
    let sourceInput := fun time => relativeBlockSourceShapeInput changed first second receiver source time
    let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate receiver
    let lower := ((7 / 8 : ℝ) - delta ^ 2 / 2 - 2 * packetTolerance - 17 * Real.exp (-(3 * growth / 4) * horizon)) * seed
    let action := fun function firstTime lastTime => ∫ time in firstTime..lastTime, Real.exp (-growth * time) * function time
    let historyError := action (fun time => ‖remainder time‖) 0 (start + horizon)
    let otherError := (constant / changed.location (receiver.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
      action (fun time => ‖fun index : Fin count => if index.val ≤ receiver.val then changed.location (index.val + 1) ^ 4 * prepared.macroSourceState time index else 0‖) 0 (start + horizon) + returnTolerance * seed / growth
    ContinuousOn relative (Icc 0 (start + horizon)) ∧ ContinuousOn remainder (Icc 0 (start + horizon)) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * ‖remainder time‖) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * ‖leading time - sourceInput time‖) volume 0 (start + horizon) ∧
    IntervalIntegrable (fun time => Real.exp (-growth * time) * (sourceInput time).1) volume 0 (start + horizon) ∧
    (∀ time ∈ Icc 0 (start + horizon), Real.exp (-growth * time) * (relative time).1 =
      action (fun current => (leading current).1) 0 time + action (fun current => (remainder current).1) 0 time) ∧
    Real.exp (-growth * start) * (relative start).1 = action (fun time => (sourceInput time).1) 0 start +
      action (fun time => (leading time).1 - (sourceInput time).1) 0 start + action (fun time => (remainder time).1) 0 start ∧
    action (fun time => (sourceInput time).1) 0 start + Real.exp (-growth * start) * lower - otherError - historyError ≤
      Real.exp (-growth * (start + horizon)) * (relative (start + horizon)).1 ∧
    (relative start).1 + lower - Real.exp (growth * start) * (otherError + historyError) ≤
      Real.exp (-growth * horizon) * (relative (start + horizon)).1 := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, returns⟩ := exists_uniform_actual_leading_driven_weighted_return
  obtain ⟨duhamelRadius, duhamelPositive, duhamelQuarter, duhamels⟩ := exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  obtain ⟨regularRadius, regularPositive, _, regularity⟩ := exists_uniform_cascade_paired_chart_regularity graphSmooth coordinateSmooth
  obtain ⟨thresholdMax, thresholdPositive, thresholdEighth, packets⟩ := exists_actual_prescribed_adjacent_signed_source_window
  let radius := min duhamelRadius regularRadius / 2
  have radiusPositive : 0 < radius := half_pos (lt_min duhamelPositive regularPositive)
  have radiusDuhamel : radius < duhamelRadius := (half_lt_self (lt_min duhamelPositive regularPositive)).trans_le (min_le_left _ _)
  have radiusRegular : radius < regularRadius := (half_lt_self (lt_min duhamelPositive regularPositive)).trans_le (min_le_right _ _)
  refine ⟨rawCap, capPositive, constant, constantNonnegative, radius, radiusPositive, radiusDuhamel.le.trans duhamelQuarter,
    thresholdMax, thresholdPositive, thresholdEighth, ?_⟩
  intro packetTolerance packetPositive packetOne scales amplitudePositive alphaPositive ratioLarge ratioPower
    referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall returnTolerance returnPositive
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans thresholdEighth
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [packets packetTolerance packetPositive packetOne scales amplitudePositive alphaPositive ratioLarge referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
      orbit sectionTime factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall,
    returns scales amplitudePositive ratioBound alphaPositive ratioPower returnPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative radiusPositive,
    eventually_gt_atTop (0 : ℝ)] with frequency packetEstimate returnEstimate leadingContinuity sourceContinuity referenceSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path prescribed receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded chartSmall timingConstant phaseTolerance angleError
    timingNonnegative phaseNonnegative angleNonnegative timingClose angleClose
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let finish := start + horizon
  let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let delta := 2 * timingConstant * phaseTolerance / changed.ratio + 2 * angleError
  let relative := fun time => referenceStraightenedShape first graph coordinate receiver time - referenceStraightenedShape second graph coordinate receiver time
  let leading := fun time => quadrupoleRelativeLeadingStrain changed first second time receiver
  let sourceInput := fun time => relativeBlockSourceShapeInput changed first second receiver source time
  let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared.toCascadeMaterialPreparedPair) graph coordinate receiver
  let lower := ((7 / 8 : ℝ) - delta ^ 2 / 2 - 2 * packetTolerance - 17 * Real.exp (-(3 * growth / 4) * horizon)) * seed
  have finishNonnegative : 0 ≤ finish := add_nonneg startNonnegative horizonNonnegative
  have nonterminal : receiver.val + 1 < count := by rw [adjacent]; exact source.isLt
  have different : receiver ≠ source := by intro same; have identity := congrArg Fin.val same; omega
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have growthPositive : 0 < growth := mul_pos (by positivity) (changed.omega_pos frequencyPositive ratioPositive _)
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| + |stableShape (cascadePairedMotion prepared.toCascadeMaterialPreparedPair side) time receiver| ≤ radius := by
    fin_cases side
    · exact chartSmall time inside
    · have actual := referenceSmall prepared.toCascadeMaterialPreparedPair time ⟨inside.1, inside.2.trans (endBound.trans path.stopBound)⟩ receiver
      change |unstableShape second time receiver| + |stableShape second time receiver| ≤ radius
      linarith only [actual, abs_nonneg (diagonalDifference second time receiver / changed.length (receiver.val + 1) ^ 2 - 1)]
  have history := duhamels prepared.toCascadeMaterialPreparedPair path receiver nonterminal finish finishNonnegative endBound
    (fun side time inside => (pairedSmall side time inside).trans_lt radiusDuhamel)
  have regular := regularity prepared.toCascadeMaterialPreparedPair path receiver finish endBound
    (fun side time inside => (pairedSmall side time inside).trans_lt radiusRegular)
  have relativeContinuous : ContinuousOn relative (Icc 0 finish) := regular.1
  have leadingContinuous : ContinuousOn leading (Icc 0 finish) :=
    (leadingContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver).mono (Icc_subset_Icc le_rfl endBound)
  have sourceContinuous : ContinuousOn sourceInput (Icc 0 finish) :=
    (sourceContinuity count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source different).mono (Icc_subset_Icc le_rfl endBound)
  have inputContinuous : ContinuousOn (fun time => leading time + remainder time) (Icc 0 finish) := history.1
  have remainderContinuous : ContinuousOn remainder (Icc 0 finish) := by
    apply (inputContinuous.sub leadingContinuous).congr
    intro time _
    change remainder time = (leading time + remainder time) - leading time
    abel
  have exponential : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have normI := (exponential.continuousOn.mul remainderContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have nonadjacentI := (exponential.continuousOn.mul (leadingContinuous.sub sourceContinuous).norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have sourceI := (exponential.continuousOn.mul sourceContinuous.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have originalHistory (time : ℝ) (inside : time ∈ Icc 0 finish) : Real.exp (-growth * time) * (relative time).1 =
      (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) +
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1 := by
    have actual : (relative time).1 = ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) * (leading current + remainder current).1 := history.2.1 time inside
    rw [actual, ← intervalIntegral.integral_const_mul]
    have identity (current : ℝ) : Real.exp (-growth * time) * (Real.exp (growth * (time - current)) * (leading current + remainder current).1) =
        Real.exp (-growth * current) * (leading current).1 + Real.exp (-growth * current) * (remainder current).1 := by
      rw [← mul_assoc, ← Real.exp_add, show -growth * time + growth * (time - current) = -growth * current by ring, Prod.fst_add, mul_add]
    simp_rw [identity]
    exact intervalIntegral.integral_add
      ((exponential.continuousOn.mul (leadingContinuous.fst.mono (Icc_subset_Icc le_rfl inside.2))).intervalIntegrable_of_Icc inside.1)
      ((exponential.continuousOn.mul (remainderContinuous.fst.mono (Icc_subset_Icc le_rfl inside.2))).intervalIntegrable_of_Icc inside.1)
  have packetData := packetEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path prescribed receiver source adjacent
    start horizon initialDistance outgoingPhase startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
    firstInitial secondInitial initialProjection initialUpper prefixBounded timingConstant phaseTolerance angleError timingNonnegative phaseNonnegative angleNonnegative timingClose angleClose
  obtain ⟨_, _, _, coefficient, _, _, _, packetLower⟩ := packetData
  have literalPacketLower : (∫ time in (0 : ℝ)..start, Real.exp (-growth * time) * (sourceInput time).1) + Real.exp (-growth * start) * lower ≤
      ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (sourceInput time).1 := by
    simpa only [prepared.referenceIdentity, sourceInput, growth, lower, delta, seed, finish, changed, first, second] using packetLower
  have nonadjacentBound := returnEstimate count phase dipoleAngle prepared path receiver source adjacent finish finishNonnegative endBound growth growthPositive
  have leadingLower (time : ℝ) : -‖leading time - sourceInput time‖ ≤ (leading time).1 - (sourceInput time).1 := by
    have projection := norm_fst_le (leading time - sourceInput time)
    simpa only [Real.norm_eq_abs, Prod.fst_sub] using (neg_abs_le ((leading time).1 - (sourceInput time).1)).trans' (neg_le_neg projection)
  have remainderLower (time : ℝ) : -‖remainder time‖ ≤ (remainder time).1 := by
    have projection : |(remainder time).1| ≤ ‖remainder time‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le (remainder time)
    exact (neg_le_neg projection).trans (neg_abs_le _)
  have result := signed_packet_lower_of_original_history startNonnegative horizonNonnegative leadingContinuous.fst sourceContinuous.fst
    remainderContinuous.fst (leadingContinuous.sub sourceContinuous).norm remainderContinuous.norm (fun time => norm_nonneg _) (fun time => norm_nonneg _)
    leadingLower remainderLower originalHistory literalPacketLower nonadjacentBound
  exact ⟨relativeContinuous, remainderContinuous, normI, nonadjacentI, sourceI, originalHistory, result⟩

end EulerNonuniqueness.Paper
