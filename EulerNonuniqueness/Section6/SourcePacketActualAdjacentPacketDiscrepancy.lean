import EulerNonuniqueness.Section6.SourcePacketBlockCenterPhysicalCost
import EulerNonuniqueness.Section6.SourcePacketPairedBlockInput
import EulerNonuniqueness.Section6.SourcePacketPhaseRobustModel
import EulerNonuniqueness.Section6.SourcePacketRetainedModel
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_actual_adjacent_packet_discrepancy_budget :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 →
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    max 2 (32768 / tolerance) ≤ scales.ratio →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon initialDistance outgoingPhase : ℝ,
    0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    2048 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ min (tolerance / 2) 1 / 5120 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
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
    let omega := changed.omega (receiver.val + 1)
    let decay := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (receiver.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let receiverPhase := phase (receiver.val + 1) - omega * start
    let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase +
      Real.arctan (1 / Real.sqrt 2) - Real.pi
    let initialMoment := ∫ position, quadrupoleDensity changed motion start source position •
      (position - quadrupoleCenter motion start source) ^ 2
    let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
    let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
      Real.sin residual * idealQuadratureInput omega seed elapsed +
        rhombusConstantMomentInput positive initialMoment frozen elapsed
    let input := fun elapsed => (relativeBlockSourceShapeInput changed motion reference receiver source (start + elapsed)).1
    ContinuousOn input (Icc 0 horizon) ∧ Continuous packet ∧
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * |input elapsed - packet elapsed|) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * |input elapsed - packet elapsed|) ≤ tolerance * seed := by
  obtain ⟨constant, constantNonnegative, chartRadius, chartPositive, comparison⟩ :=
    exists_source_packet_weighted_physical_comparison
  obtain ⟨physicalRadius, physicalPositive, physicalEighth, physicalFactory⟩ :=
    exists_source_packet_blockcenter_reference_frame_physical_cost
  obtain ⟨referenceRadius, referencePositive, _, referenceFactory⟩ :=
    exists_reference_block_source_input_frozen_budget
  let radius := min physicalRadius referenceRadius
  refine ⟨radius, lt_min physicalPositive referencePositive, (min_le_left _ _).trans physicalEighth, ?_⟩
  intro tolerance tolerancePositive _toleranceOne scales amplitudePositive alphaPositive ratioLarge
    referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have referenceRatio : max 2 (16384 / (tolerance / 2)) ≤ scales.ratio := by
    (convert ratioLarge using 1; congr 1; field_simp; ring)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  have thresholdSmall : threshold ≤ 1 / 8 := thresholdBound.trans ((min_le_left _ _).trans physicalEighth)
  filter_upwards [physicalFactory scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative
      amplitudeBound threshold (thresholdBound.trans (min_le_left _ _)) orbit sectionTime factor scaleRoot boundaryConstant
      1 radiusFactor constant chartRadius (tolerance / 2) initialError factorPositive factorSmall rootOne boundaryOne
      (by norm_num) radiusFactorPositive constantNonnegative chartPositive (by positivity) initialErrorSmall,
    referenceFactory scales amplitudePositive alphaPositive (tolerance / 2) (by positivity) referenceRatio referenceConstant
      referenceNonnegative amplitudeBound threshold (thresholdBound.trans (min_le_right _ _)),
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne]
    with frequency physicalEstimate referenceEstimate inputContinuous
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
  let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let initialMoment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
  let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
    Real.sin residual * idealQuadratureInput omega seed elapsed + rhombusConstantMomentInput positive initialMoment frozen elapsed
  let input := fun elapsed => (relativeBlockSourceShapeInput changed motion reference receiver source (start + elapsed)).1
  let referenceInput := fun elapsed => referenceBlockSourceInput changed reference receiver source (start + elapsed)
  obtain ⟨geometry, normalization, physicalIntegrable, physicalBound⟩ :=
    physicalEstimate count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
      startNonnegative horizonNonnegative endBound initialDistanceLarge initialDistanceSmall ratioBudget initialBudget
      firstInitial secondInitial initialProjection initialUpper prefixBounded
  have frozenIdentity : geometry.frozenDisplacement = frozen := by
    rw [normalization.frozenDisplacement, adjacent]
  have omegaPositive : 0 < omega := changed.omega_pos geometry.frequencyPositive geometry.ratioPositive _
  have seedIdentity : seed = Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * ‖frozen‖ ^ 4) := by
    simp only [seed, Scales.seed, omega, frozen, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 := Complex.exp_ne_zero _
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
    exact ((continuous_const.mul (idealGrowingInput_continuous omega seed)).add
      (continuous_const.mul (by unfold idealQuadratureInput; fun_prop))).add
        (rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero initialMoment frozen)
  have different : receiver ≠ source := by intro equality; have same := congrArg Fin.val equality; omega
  have inputC0 : ContinuousOn input (Icc 0 horizon) := by
    have actual := (inputContinuous count phase dipoleAngle prepared path receiver source different).fst
    rw [prepared.referenceIdentity] at actual
    apply actual.comp (continuous_const.add continuous_id).continuousOn
    intro elapsed member
    change 0 ≤ start + elapsed ∧ start + elapsed ≤ path.stop
    exact ⟨by linarith only [startNonnegative, member.1], by linarith only [endBound, member.2]⟩
  have weightContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have discrepancyIntegrable := (weightContinuous.continuousOn.mul
    (inputC0.sub packetContinuous.continuousOn).abs).intervalIntegrable_of_Icc (μ := volume) horizonNonnegative
  obtain ⟨physicalErrorIntegrable, physicalErrorBound⟩ := comparison geometry horizonNonnegative physicalIntegrable
  obtain ⟨referenceIntegrable, referenceBound⟩ := referenceEstimate prepared.referenceWitness receiver source adjacent start horizon
    startNonnegative horizonNonnegative (endBound.trans path.stopBound)
  have pairIdentity (elapsed : ℝ) : input elapsed = geometry.actualInput elapsed - referenceInput elapsed :=
    normalization.paired_source_input_identity elapsed
  have physicalBudget : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      |geometry.actualInput elapsed - geometry.modelInput elapsed|) ≤ (tolerance / 2) * seed := by
    apply physicalErrorBound.trans
    rw [seedIdentity]
    simpa only [decay, omega, frozen, changed, adjacent] using physicalBound
  have referenceBudget : (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * |referenceInput elapsed|) ≤
      (tolerance / 2) * seed := by
    rw [seedIdentity]
    simpa only [referenceInput, decay, omega, frozen, reference, changed, adjacent] using referenceBound
  have comparisonBound := intervalIntegral.integral_mono_on horizonNonnegative discrepancyIntegrable
    (physicalErrorIntegrable.add referenceIntegrable) (by
      intro elapsed _
      have identity : input elapsed - packet elapsed =
          (geometry.actualInput elapsed - geometry.modelInput elapsed) - referenceInput elapsed := by
        rw [pairIdentity, modelEquation]
        ring
      rw [identity]
      have triangle := mul_le_mul_of_nonneg_left
        (abs_sub (geometry.actualInput elapsed - geometry.modelInput elapsed) (referenceInput elapsed))
        (Real.exp_pos (-decay * elapsed)).le
      simpa only [mul_add] using triangle)
  rw [intervalIntegral.integral_add physicalErrorIntegrable referenceIntegrable] at comparisonBound
  exact ⟨inputC0, packetContinuous, discrepancyIntegrable, by linarith only [comparisonBound, physicalBudget, referenceBudget]⟩

end EulerNonuniqueness.Paper
