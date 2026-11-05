import EulerNonuniqueness.Section6.SourcePacketActualInheritedMoment
import EulerNonuniqueness.Section6.SourcePacketPhaseRobustTail
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem retained_coefficient_window_translation (input : ℝ → ℝ) (rate start horizon : ℝ) :
    (∫ time in start..start + horizon, Real.exp (-rate * time) * input time) =
      Real.exp (-rate * start) * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-rate * elapsed) * input (start + elapsed) := by
  have shift := intervalIntegral.integral_comp_add_left
    (f := fun time => Real.exp (-rate * time) * input time) (a := 0) (b := horizon) start
  rw [add_zero] at shift
  rw [← shift, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro elapsed _
  dsimp only
  rw [show -rate * (start + elapsed) = -rate * start + -rate * elapsed by ring, Real.exp_add]
  ring

theorem eventually_actual_retained_signed_coefficient
    (coefficientTolerance : ℝ) (tolerancePositive : 0 < coefficientTolerance) (toleranceSmall : coefficientTolerance ≤ 1 / 8)
    (scales : Scales) (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start ∈ Icc 0 path.stop, ∀ initialDistance outgoingPhase : ℝ, 32 ≤ initialDistance →
    12 * initialDistance ≤ coefficientTolerance * scales.ratio →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    let omega := changed.omega (receiver.val + 1)
    let decay := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (receiver.val + 1)
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let receiverPhase := phase (receiver.val + 1) - omega * start
    let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let moment := ∫ position, quadrupoleDensity changed motion start source position • (position - quadrupoleCenter motion start source) ^ 2
    let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
    let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
      Real.sin residual * idealQuadratureInput omega seed elapsed + rhombusConstantMomentInput positive moment frozen elapsed
    let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
    let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
    let windowCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
    let originalCoefficient := prefixIntegral + Real.exp (-decay * start) * windowCoefficient
    ContinuousOn input (Icc 0 path.stop) ∧ Continuous packet ∧
    IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * packet elapsed) (Ioi 0) ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 start ∧
    windowCoefficient = seed * Real.cos residual +
      ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment frozen elapsed ∧
    |windowCoefficient - seed * Real.cos residual| ≤ coefficientTolerance * seed ∧
    |Real.exp (decay * start) * originalCoefficient / seed - Real.cos residual| ≤
      coefficientTolerance + Real.exp (decay * start) * |prefixIntegral| / seed ∧
    ∀ horizon : ℝ, 0 ≤ horizon → start + horizon ≤ path.stop →
      IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 (start + horizon) ∧
      IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed|) volume 0 horizon ∧
      |(∫ time in (0 : ℝ)..start + horizon, Real.exp (-decay * time) * input time) - originalCoefficient| ≤
        Real.exp (-decay * start) * ((∫ elapsed in (0 : ℝ)..horizon,
          Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed|) +
            17 * seed * Real.exp (-(3 * decay / 4) * horizon)) := by
  filter_upwards [scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (zero_lt_one.trans_le rootOne) (zero_le_one.trans boundaryOne) tolerancePositive,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall, eventually_gt_atTop (0 : ℝ)]
    with frequency inherited sourceContinuous frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start startInside initialDistance outgoingPhase initialLarge ratioBudget
  dsimp only
  intro firstInitial secondInitial centerBound
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
  let moment := ∫ position, quadrupoleDensity changed motion start source position • (position - quadrupoleCenter motion start source) ^ 2
  let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
  let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
    Real.sin residual * idealQuadratureInput omega seed elapsed + rhombusConstantMomentInput positive moment frozen elapsed
  let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
  let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
  let windowCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
  let originalCoefficient := prefixIntegral + Real.exp (-decay * start) * windowCoefficient
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive : 0 < omega := changed.omega_pos frequencyPositive ratioPositive _
  have decayPositive : 0 < decay := by dsimp only [decay]; positivity
  have frozenNorm : ‖frozen‖ = changed.location (source.val + 1) := by
    dsimp only [frozen]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, changed.adjacent_location_distance]
  have frozenNonzero : frozen ≠ 0 := norm_pos_iff.mp (by rw [frozenNorm]; exact changed.location_pos _)
  have seedIdentity : seed = Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * omega ^ 2 * ‖frozen‖ ^ 4) := by
    simp only [seed, Scales.seed, omega, frozen, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have seedPositive : 0 < seed := by
    rw [seedIdentity]
    have := changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)
    have := norm_pos_iff.mpr frozenNonzero
    positivity
  have positiveContinuous : Continuous positive := by dsimp only [positive]; fun_prop
  have positiveNonzero (elapsed : ℝ) : positive elapsed ≠ 0 := Complex.exp_ne_zero _
  have momentSmall := inherited count phase dipoleAngle prepared path source start startInside initialDistance initialLarge ratioBudget
    (Complex.exp (Complex.I * (outgoingPhase : ℂ))) frozen (by rw [Complex.norm_exp]; simp) frozenNonzero
    firstInitial secondInitial centerBound
  have momentBound : 6 * ‖moment‖ / (Real.pi * ‖frozen‖ ^ 4 * decay) ≤ coefficientTolerance * seed := by
    rw [seedIdentity]
    exact momentSmall
  have retained := rhombusConstantMomentInput_weighted_bound positiveContinuous positiveNonzero moment frozen decayPositive
  let growing := fun elapsed => Real.exp (-decay * elapsed) * idealGrowingInput omega seed elapsed
  let quadrature := fun elapsed => Real.exp (-decay * elapsed) * idealQuadratureInput omega seed elapsed
  let retainedInput := fun elapsed => Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment frozen elapsed
  have growingIntegrable : IntegrableOn growing (Ioi 0) := idealGrowingInput_weighted_integrable omega seed omegaPositive
  have quadratureIntegrable : IntegrableOn quadrature (Ioi 0) := idealQuadratureInput_weighted_integrable omega seed omegaPositive
  have packetContinuous : Continuous packet := by
    exact ((continuous_const.mul (idealGrowingInput_continuous omega seed)).add
      (continuous_const.mul (by unfold idealQuadratureInput; fun_prop))).add
        (rhombusConstantMomentInput_continuous positiveContinuous positiveNonzero moment frozen)
  have integrandIdentity : (fun elapsed => Real.exp (-decay * elapsed) * packet elapsed) =
      fun elapsed => Real.cos residual * growing elapsed + Real.sin residual * quadrature elapsed + retainedInput elapsed := by
    funext elapsed
    dsimp only [packet, growing, quadrature, retainedInput]
    ring
  have packetIntegrable : IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * packet elapsed) (Ioi 0) := by
    rw [integrandIdentity]
    exact ((growingIntegrable.const_mul (Real.cos residual)).add (quadratureIntegrable.const_mul (Real.sin residual))).add retained.1
  have coefficientIdentity : windowCoefficient = seed * Real.cos residual +
      ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive moment frozen elapsed := by
    dsimp only [windowCoefficient]
    rw [integrandIdentity, integral_add (f := fun elapsed => Real.cos residual * growing elapsed + Real.sin residual * quadrature elapsed)
        (g := retainedInput) ((growingIntegrable.const_mul _).add (quadratureIntegrable.const_mul _)) retained.1,
      integral_add (f := fun elapsed => Real.cos residual * growing elapsed) (g := fun elapsed => Real.sin residual * quadrature elapsed)
        (growingIntegrable.const_mul _) (quadratureIntegrable.const_mul _), integral_const_mul, integral_const_mul,
      show (∫ elapsed in Ioi 0, growing elapsed) = seed from idealGrowingInput_weighted_integral omega seed omegaPositive,
      show (∫ elapsed in Ioi 0, quadrature elapsed) = 0 from idealQuadratureInput_weighted_integral omega seed omegaPositive]
    dsimp only [retainedInput]
    ring
  have coefficientBound : |windowCoefficient - seed * Real.cos residual| ≤ coefficientTolerance * seed := by
    rw [coefficientIdentity, add_sub_cancel_left]
    exact retained.2.trans momentBound
  have different : receiver ≠ source := by intro equality; have := congrArg Fin.val equality; omega
  have inputContinuous : ContinuousOn input (Icc 0 path.stop) := by
    have actual := (sourceContinuous count phase dipoleAngle prepared path receiver source different).fst
    rw [prepared.referenceIdentity] at actual
    exact actual
  have weightedContinuous : ContinuousOn (fun time => Real.exp (-decay * time) * input time) (Icc 0 path.stop) :=
    (show Continuous (fun time : ℝ => Real.exp (-decay * time)) by fun_prop).continuousOn.mul inputContinuous
  have prefixIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 start :=
    (weightedContinuous.mono (Icc_subset_Icc le_rfl startInside.2)).intervalIntegrable_of_Icc startInside.1
  have exponentialCancellation : Real.exp (decay * start) * Real.exp (-decay * start) = 1 := by
    rw [← Real.exp_add, show decay * start + -decay * start = 0 by ring, Real.exp_zero]
  have normalized : |Real.exp (decay * start) * originalCoefficient / seed - Real.cos residual| ≤
      coefficientTolerance + Real.exp (decay * start) * |prefixIntegral| / seed := by
    have windowBound : |windowCoefficient / seed - Real.cos residual| ≤ coefficientTolerance := by
      rw [show windowCoefficient / seed - Real.cos residual = (windowCoefficient - seed * Real.cos residual) / seed by field_simp,
        abs_div, abs_of_pos seedPositive]
      exact (div_le_iff₀ seedPositive).mpr coefficientBound
    have identity : Real.exp (decay * start) * originalCoefficient / seed - Real.cos residual =
        (windowCoefficient / seed - Real.cos residual) + Real.exp (decay * start) * prefixIntegral / seed := by
      dsimp only [originalCoefficient]
      rw [mul_add, ← mul_assoc, exponentialCancellation, one_mul]
      ring
    rw [identity]
    have triangle := abs_add (windowCoefficient / seed - Real.cos residual) (Real.exp (decay * start) * prefixIntegral / seed)
    rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos seedPositive] at triangle
    exact triangle.trans (add_le_add_right windowBound _)
  refine ⟨inputContinuous, packetContinuous, packetIntegrable, prefixIntegrable, coefficientIdentity, coefficientBound, normalized, ?_⟩
  intro horizon horizonNonnegative endBound
  have windowRange : (fun elapsed : ℝ => start + elapsed) '' Icc 0 horizon ⊆ Icc 0 path.stop := by
    rintro time ⟨elapsed, inside, rfl⟩
    change 0 ≤ start + elapsed ∧ start + elapsed ≤ path.stop
    exact ⟨by linarith only [startInside.1, inside.1], by linarith only [endBound, inside.2]⟩
  have windowContinuous := inputContinuous.comp (continuous_const.add continuous_id).continuousOn
    (fun elapsed inside => windowRange ⟨elapsed, inside, rfl⟩)
  have weightContinuous : Continuous (fun elapsed : ℝ => Real.exp (-decay * elapsed)) := by fun_prop
  have actualWindowIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * input (start + elapsed)) volume 0 horizon :=
    (weightContinuous.continuousOn.mul windowContinuous).intervalIntegrable_of_Icc horizonNonnegative
  have modelWindowIntegrable := (weightContinuous.mul packetContinuous).intervalIntegrable (μ := volume) 0 horizon
  have discrepancyIntegrable : IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed|) volume 0 horizon :=
    (weightContinuous.continuousOn.mul
    (windowContinuous.sub packetContinuous.continuousOn).abs).intervalIntegrable_of_Icc horizonNonnegative
  have originalIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 (start + horizon) :=
    (weightedContinuous.mono (Icc_subset_Icc le_rfl endBound)).intervalIntegrable_of_Icc (by linarith only [startInside.1, horizonNonnegative])
  have physicalWindowIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume start (start + horizon) :=
    (weightedContinuous.mono (Icc_subset_Icc startInside.1 endBound)).intervalIntegrable_of_Icc (by linarith only [horizonNonnegative])
  have tail := (phase_retained_moment_packet_tail positiveContinuous positiveNonzero moment frozen (offset := residual)
    omegaPositive seedPositive.le horizonNonnegative (momentBound.trans (by nlinarith only [mul_le_mul_of_nonneg_right toleranceSmall seedPositive.le]))).2.2
  have originalSplit : (∫ time in (0 : ℝ)..start + horizon, Real.exp (-decay * time) * input time) =
      prefixIntegral + Real.exp (-decay * start) * ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals prefixIntegrable physicalWindowIntegrable,
      retained_coefficient_window_translation]
  have discrepancyBound : |(∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed)) -
      ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * packet elapsed| ≤
        ∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed| := by
    rw [← intervalIntegral.integral_sub actualWindowIntegrable modelWindowIntegrable]
    have bound := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
      (f := fun elapsed => Real.exp (-decay * elapsed) * input (start + elapsed) - Real.exp (-decay * elapsed) * packet elapsed) horizonNonnegative
    simpa only [← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)] using bound
  refine ⟨originalIntegrable, discrepancyIntegrable, ?_⟩
  have compared := (abs_sub_le
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed))
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * packet elapsed) windowCoefficient).trans
      (add_le_add discrepancyBound tail)
  rw [originalSplit]
  change |prefixIntegral + Real.exp (-decay * start) * _ - (prefixIntegral + Real.exp (-decay * start) * windowCoefficient)| ≤ _
  rw [show prefixIntegral + Real.exp (-decay * start) * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed)) -
      (prefixIntegral + Real.exp (-decay * start) * windowCoefficient) = Real.exp (-decay * start) *
        ((∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * input (start + elapsed)) - windowCoefficient) by ring,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left compared (Real.exp_pos _).le

end EulerNonuniqueness.Paper
