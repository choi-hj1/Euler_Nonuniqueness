import EulerNonuniqueness.Section6.SourcePacketBlockCenterPhysicalCost
import EulerNonuniqueness.Section6.SourcePacketPairedBlockInput
import EulerNonuniqueness.Section6.SourcePacketPhaseRobustTail
import EulerNonuniqueness.Section6.SourcePacketPhaseRobustModel
import EulerNonuniqueness.Section6.SourcePacketRetainedModel
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_actual_adjacent_signed_source_window :
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
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
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
    let decay := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let residual := 4 * Complex.arg frozen -
      2 * (phase (receiver.val + 1) - changed.omega (receiver.val + 1) * start) -
      2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let input := fun elapsed => (relativeBlockSourceShapeInput changed motion
      prepared.referenceWitness.trajectory.movingFamily.patchMotion receiver source (start + elapsed)).1
    ContinuousOn input (Icc 0 horizon) ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * input elapsed) volume 0 horizon ∧
    ∃ coefficient : ℝ,
      |coefficient - seed * Real.cos residual| ≤ seed / 8 ∧ coefficient ≤ (9 / 8 : ℝ) * seed ∧
      |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input elapsed) - coefficient| ≤
        2 * tolerance * seed + 17 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
  obtain ⟨constant, constantNonnegative, chartRadius, chartPositive, comparison⟩ :=
    exists_source_packet_signed_physical_comparison
  obtain ⟨physicalRadius, physicalPositive, physicalEighth, physicalFactory⟩ :=
    exists_source_packet_blockcenter_reference_frame_physical_cost
  obtain ⟨referenceRadius, referencePositive, _, referenceFactory⟩ :=
    exists_reference_block_source_input_frozen_budget
  let radius := min physicalRadius referenceRadius
  refine ⟨radius, lt_min physicalPositive referencePositive, (min_le_left _ _).trans physicalEighth, ?_⟩
  intro tolerance tolerancePositive toleranceOne scales amplitudePositive alphaPositive ratioLarge
    referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans ((min_le_left _ _).trans physicalEighth)
  filter_upwards [physicalFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative
      amplitudeBound threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime factor scaleRoot boundaryConstant
      1 radiusFactor constant chartRadius tolerance initialError factorPositive factorSmall rootOne boundaryOne
      (by norm_num) radiusFactorPositive constantNonnegative chartPositive tolerancePositive initialErrorSmall,
    referenceFactory scales amplitudePositive alphaPositive tolerance tolerancePositive ratioLarge referenceConstant
      referenceNonnegative amplitudeBound threshold (thresholdBound.trans (min_le_right _ _)),
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorOne (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne)
      (by norm_num : (0 : ℝ) < 1 / 8),
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne]
    with frequency physicalEstimate referenceEstimate inherited inputContinuous
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded
  rw [adjacent]
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let omega := changed.omega source.val
  let decay := 2 * Real.sqrt 2 * omega
  let seed := changed.seed source.val
  let frozen : ℂ := (changed.location source.val : ℂ) - (changed.location (source.val + 1) : ℂ)
  let receiverPhase := phase source.val - omega * start
  let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase +
    Real.arctan (1 / Real.sqrt 2) - Real.pi
  let input := fun elapsed => (relativeBlockSourceShapeInput changed motion reference receiver source (start + elapsed)).1
  let referenceInput := fun elapsed => referenceBlockSourceInput changed reference receiver source (start + elapsed)
  have seedIdentity : seed = Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * ‖frozen‖ ^ 4) := by
    simp only [seed, Scales.seed, omega, frozen, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have seedNonnegative : 0 ≤ seed := by rw [seedIdentity]; positivity
  have distancePositive : 0 < initialDistance := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2048) initialDistanceLarge
  have ratioPhysical : 12 * initialDistance ≤ scales.ratio := by linarith only [ratioBudget, distancePositive]
  obtain ⟨geometry, normalization, physicalIntegrable, physicalBound⟩ :=
    physicalEstimate count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
      startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioPhysical initialBudget
      firstInitial secondInitial initialProjection initialUpper prefixBounded
  have frozenIdentity : geometry.frozenDisplacement = frozen := by
    rw [normalization.frozenDisplacement, adjacent]
  have omegaPositive : 0 < omega := changed.omega_pos geometry.frequencyPositive geometry.ratioPositive _
  have positiveContinuous : Continuous (fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))) := by fun_prop
  have positiveNonzero (elapsed : ℝ) : Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ)) ≠ 0 :=
    Complex.exp_ne_zero _
  have firstCoarse : ‖firstDipoleSeparation motion start source -
      ((changed.length (source.val + 1) : ℝ) : ℂ) * Complex.exp (Complex.I * (outgoingPhase : ℂ))‖ ≤
        changed.length (source.val + 1) / 64 :=
    firstInitial.trans (by nlinarith only [mul_le_mul_of_nonneg_right initialErrorSmall (changed.length_pos (source.val + 1)).le])
  have secondCoarse : ‖secondDipoleSeparation motion start source -
      ((changed.length (source.val + 1) : ℝ) : ℂ) * (-Complex.exp (Complex.I * (outgoingPhase : ℂ)))‖ ≤
        changed.length (source.val + 1) / 64 :=
    secondInitial.trans (by nlinarith only [mul_le_mul_of_nonneg_right initialErrorSmall (changed.length_pos (source.val + 1)).le])
  have momentSmall := inherited count phase dipoleAngle prepared path source start
    ⟨startNonnegative, by linarith only [endBound, horizonNonnegative]⟩ initialDistance
    (by linarith only [initialDistanceLarge]) (by linarith only [ratioBudget])
    (Complex.exp (Complex.I * (outgoingPhase : ℂ))) frozen
    (by rw [Complex.norm_exp]; simp) (frozenIdentity ▸ geometry.frozenNonzero)
    firstCoarse secondCoarse initialUpper
  let initialMoment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  have momentBound : 6 * ‖initialMoment‖ / (Real.pi * ‖frozen‖ ^ 4 * decay) ≤ seed / 8 := by
    rw [seedIdentity]
    convert momentSmall using 1 <;> dsimp only [initialMoment, decay, omega, changed, motion] <;> ring
  let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
  let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
    Real.sin residual * idealQuadratureInput omega seed elapsed +
      rhombusConstantMomentInput positive initialMoment frozen elapsed
  have positiveIdentity : geometry.idealPositive = positive := by
    rw [normalization.idealPositive]
    funext elapsed
    dsimp only [positive, receiverPhase, omega]
    rw [adjacent]
    congr 2
    push_cast
    ring
  have modelEquation (elapsed : ℝ) : geometry.modelInput elapsed = packet elapsed := by
    unfold SourcePacketPhysicalGeometry.modelInput
    rw [normalization.targetMoment, positiveIdentity, frozenIdentity]
    have model := retained_moment_model_input_eq_packet initialMoment frozen 1 omega
      (changed.circulation (source.val + 1)) receiverPhase outgoingPhase elapsed
      (frozenIdentity ▸ geometry.frozenNonzero)
    simp only [Complex.ofReal_one, one_mul] at model
    change rhombusConstantMomentInput positive
      (initialMoment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed) frozen elapsed = packet elapsed
    rw [model, rotatingRhombusGrowingStrainInput_phase_decomposition (by norm_num : (1 : ℝ) ≠ 0) omega
      (changed.circulation (source.val + 1)) ‖frozen‖ (Complex.arg frozen) receiverPhase outgoingPhase elapsed
      omegaPositive (norm_pos_iff.mpr (frozenIdentity ▸ geometry.frozenNonzero))]
    rw [← seedIdentity]
  have packetContinuous : Continuous packet := by
    dsimp only [packet]
    apply Continuous.add
    · apply Continuous.add
      · exact continuous_const.mul (idealGrowingInput_continuous omega seed)
      · unfold idealQuadratureInput
        fun_prop
    · exact rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero initialMoment frozen
  have modelIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * geometry.modelInput elapsed) volume 0 horizon := by
    simp_rw [modelEquation]
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul packetContinuous).intervalIntegrable _ _
  have physicalIntegrable' : IntervalIntegrable
      (fun elapsed => Real.exp (-decay * elapsed) * geometry.physicalCost constant elapsed) volume 0 horizon := physicalIntegrable
  obtain ⟨actualIntegrable, actualComparison⟩ := comparison geometry horizonNonnegative physicalIntegrable' modelIntegrable
  have direct := phase_retained_moment_packet_tail positiveContinuous positiveNonzero initialMoment frozen
    (offset := residual) omegaPositive seedNonnegative horizonNonnegative momentBound
  let coefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
  have modelTail : |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) -
      coefficient| ≤ 17 * seed * Real.exp (-(3 * decay / 4) * horizon) := by
    simp_rw [modelEquation]
    exact direct.2.2
  have different : receiver ≠ source := by intro identity; have same := congrArg Fin.val identity; omega
  have inputC0 : ContinuousOn input (Icc 0 horizon) := by
    have actual := (inputContinuous count phase dipoleAngle prepared path receiver source different).fst
    rw [prepared.referenceIdentity] at actual
    apply actual.comp (continuous_const.add continuous_id).continuousOn
    intro elapsed member
    change 0 ≤ start + elapsed ∧ start + elapsed ≤ path.stop
    exact ⟨by linarith only [startNonnegative, member.1], by linarith only [endBound, member.2]⟩
  have inputIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * input elapsed) volume 0 horizon :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul inputC0).intervalIntegrable_of_Icc horizonNonnegative
  have pairIdentity (elapsed : ℝ) : input elapsed = geometry.actualInput elapsed - referenceInput elapsed :=
    normalization.paired_source_input_identity elapsed
  have referenceIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * referenceInput elapsed) volume 0 horizon := by
    convert actualIntegrable.sub inputIntegrable using 1
    ext elapsed
    rw [pairIdentity]
    ring
  obtain ⟨referenceAbsoluteIntegrable, referenceBound⟩ := referenceEstimate prepared.referenceWitness receiver source adjacent start horizon
    startNonnegative horizonNonnegative (endBound.trans path.stopBound)
  have physicalBudget : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      geometry.physicalCost constant elapsed) ≤ tolerance * seed := by
    rw [seedIdentity]
    simpa only [decay, omega, frozen, changed, adjacent] using physicalBound
  have referenceBudget : |∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * referenceInput elapsed| ≤ tolerance * seed := by
    have estimate := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun elapsed =>
      Real.exp (-decay * elapsed) * referenceInput elapsed) horizonNonnegative
    simp only [abs_mul, abs_of_pos (Real.exp_pos _)] at estimate
    apply estimate.trans
    rw [seedIdentity]
    simpa only [referenceInput, decay, omega, frozen, reference, changed, adjacent] using referenceBound
  have integralPair : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input elapsed) =
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) -
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * referenceInput elapsed := by
    rw [← intervalIntegral.integral_sub actualIntegrable referenceIntegrable]
    apply intervalIntegral.integral_congr
    intro elapsed _
    dsimp only
    rw [pairIdentity, mul_sub]
  refine ⟨inputC0, inputIntegrable, coefficient, direct.1, direct.2.1, ?_⟩
  rw [integralPair]
  have triangle := abs_sub_le
    ((∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) -
      ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * referenceInput elapsed)
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) coefficient
  have firstError : |((∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed) -
      ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * referenceInput elapsed) -
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed)| ≤ tolerance * seed := by
    simpa only [sub_sub_cancel_left, abs_neg] using referenceBudget
  have secondError := (abs_sub_le
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.actualInput elapsed)
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * geometry.modelInput elapsed) coefficient).trans
      (add_le_add (actualComparison.trans physicalBudget) modelTail)
  linarith only [triangle, firstError, secondError]

end EulerNonuniqueness.Paper

