import EulerNonuniqueness.Section5.CascadeAdjacentIncomingPrefixSeedBudget
import EulerNonuniqueness.Section6.SourcePacketActualRetainedSignedCoefficient
import EulerNonuniqueness.Section5.Delay

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_prefix_coefficient_budget :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent ≥ (1 : ℝ),
    ∀ coefficientTolerance : ℝ, 0 < coefficientTolerance → coefficientTolerance ≤ 1 / 8 →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start ∈ Icc 0 path.stop, ∀ coefficient magnitude initialDistance outgoingPhase : ℝ,
    0 < coefficient → 0 ≤ magnitude → 32 ≤ initialDistance →
    12 * initialDistance ≤ coefficientTolerance * scales.ratio →
    (∀ time ∈ Icc 0 start, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ time ∈ Icc 0 start, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
          extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let omega := changed.omega (receiver.val + 1)
    let decay := 2 * Real.sqrt 2 * omega
    let seed := changed.seed (receiver.val + 1)
    let direction := Complex.exp (Complex.I * (outgoingPhase : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * initialDistance →
    let sourceRate := coefficient * changed.omega (source.val + 1)
    let state := fun time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed motion prepared.reference source time‖ +
      ‖quadrupoleCenter motion time source - quadrupoleCenter prepared.reference time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    2 * decay ≤ sourceRate →
    (∀ time ∈ Icc 0 start, state time ≤ magnitude * Real.exp (sourceRate * (time - start))) →
    let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let receiverPhase := phase (receiver.val + 1) - omega * start
    let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
    let moment := ∫ position, quadrupoleDensity changed motion start source position • (position - quadrupoleCenter motion start source) ^ 2
    let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
    let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
      Real.sin residual * idealQuadratureInput omega seed elapsed + rhombusConstantMomentInput positive moment frozen elapsed
    let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
    let forcing := prepared.selectedForeignForcing {source} receiver
    let observation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ +
      ∑ patch : Fin 4, ‖patchCentroid motion time receiver patch - patchCentroid prepared.reference time receiver patch‖
    let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
    let observationIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * observation time
    let windowCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
    let originalCoefficient := prefixIntegral + Real.exp (-decay * start) * windowCoefficient
    ContinuousOn input (Icc 0 path.stop) ∧ ContinuousOn forcing (Icc 0 start) ∧ ContinuousOn observation (Icc 0 start) ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 start ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * forcing time) volume 0 start ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * observation time) volume 0 start ∧
    |prefixIntegral| ≤ ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * forcing time ∧
    |prefixIntegral| ≤ (100 * constant / coefficient) * extent ^ 2 * (seed / changed.ratio ^ 2) *
      magnitude * Real.exp (-decay * start) +
        constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 * observationIntegral ∧
    |Real.exp (decay * start) * originalCoefficient / seed - Real.cos residual| ≤ coefficientTolerance +
      (100 * constant / coefficient) * extent ^ 2 * magnitude / changed.ratio ^ 2 +
        (Real.exp (decay * start) / seed) *
          (constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5) * observationIntegral := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, prefixFactory⟩ :=
    exists_uniform_actual_adjacent_incoming_prefix_seed_budget
  refine ⟨rawCap, capPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne coefficientTolerance tolerancePositive toleranceSmall scales amplitudePositive ratioBound alphaPositive
    orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [prefixFactory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_actual_retained_signed_coefficient coefficientTolerance tolerancePositive toleranceSmall scales amplitudePositive ratioBound
      alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency prefixes retained frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start startInside
    coefficient magnitude initialDistance outgoingPhase coefficientPositive magnitudeNonnegative initialLarge ratioBudget referenceExtent alternativeExtent
  dsimp only
  intro firstInitial secondInitial centerBound rateSeparated profile
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let length := changed.length (source.val + 1)
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let omega := changed.omega (receiver.val + 1)
  let decay := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (receiver.val + 1)
  let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
  let forcing := prepared.selectedForeignForcing {source} receiver
  let observation := fun time => ‖quadrupoleCenter motion time receiver - quadrupoleCenter prepared.reference time receiver‖ +
    ∑ patch : Fin 4, ‖patchCentroid motion time receiver patch - patchCentroid prepared.reference time receiver patch‖
  let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
  let observationIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * observation time
  let observerCoefficient := constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5
  let sourceTerm := (100 * constant / coefficient) * extent ^ 2 * (seed / changed.ratio ^ 2) * magnitude * Real.exp (-decay * start)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  have decayPositive : 0 < decay := by
    have := changed.omega_pos frequencyPositive ratioPositive (receiver.val + 1)
    dsimp only [decay, omega]
    positivity
  obtain ⟨inputContinuous, _, _, inputIntegrable, _, _, normalized, _⟩ :=
    retained count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source adjacent start startInside
      initialDistance outgoingPhase initialLarge ratioBudget firstInitial secondInitial centerBound
  obtain ⟨forcingContinuous, observationContinuous, forcingIntegrable, observationIntegrable, prefixBudget⟩ :=
    prefixes count phase dipoleAngle prepared path receiver source adjacent start coefficient magnitude decay startInside.1 startInside.2
      coefficientPositive magnitudeNonnegative decayPositive.le referenceExtent alternativeExtent rateSeparated profile
  have forcingDominates (time : ℝ) : |input time| ≤ forcing time := by
    have component : |input time| ≤ ‖relativeBlockSourceShapeInput changed motion prepared.reference receiver source time‖ := by
      dsimp only [input]
      rw [prepared.referenceIdentity]
      simpa only [Real.norm_eq_abs] using norm_fst_le (relativeBlockSourceShapeInput changed motion reference receiver source time)
    have extraNonnegative : 0 ≤ forcing time - ‖relativeBlockSourceShapeInput changed motion prepared.reference receiver source time‖ := by
      have locationPositive := changed.location_pos (receiver.val + 1)
      have addBound (first second third fourth fifth sixth : ℝ)
          (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third)
          (fourthNonnegative : 0 ≤ fourth) (fifthNonnegative : 0 ≤ fifth)
          (sixthNonnegative : 0 ≤ sixth) : first ≤ first + second + third + fourth + fifth + sixth := by
        linarith only [secondNonnegative, thirdNonnegative, fourthNonnegative, fifthNonnegative, sixthNonnegative]
      apply sub_nonneg.mpr
      dsimp only [forcing, CascadeSourcePreparedPair.selectedForeignForcing,
        CascadeSourcePreparedPair.coarserBlockCoefficientTerm, CascadeSourcePreparedPair.coarserPatchCoefficientTerm]
      simp only [Finset.sum_singleton]
      apply addBound <;> positivity
    exact component.trans (sub_nonneg.mp extraNonnegative)
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-decay * time)) := by fun_prop
  have absoluteIntegrable : IntervalIntegrable (fun time => Real.exp (-decay * time) * |input time|) volume 0 start :=
    (exponentialContinuous.continuousOn.mul (inputContinuous.abs.mono (Icc_subset_Icc le_rfl startInside.2))).intervalIntegrable_of_Icc startInside.1
  have absolutePrefix := intervalIntegral.abs_integral_le_integral_abs (μ := volume)
    (f := fun time => Real.exp (-decay * time) * input time) startInside.1
  simp only [abs_mul, abs_of_pos (Real.exp_pos _)] at absolutePrefix
  have integralComparison := intervalIntegral.integral_mono_on startInside.1 absoluteIntegrable forcingIntegrable
    (fun time _ => mul_le_mul_of_nonneg_left (forcingDominates time) (Real.exp_pos _).le)
  have prefixComparison : |prefixIntegral| ≤ ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * forcing time :=
    absolutePrefix.trans integralComparison
  have prefixBound : |prefixIntegral| ≤ sourceTerm + observerCoefficient * observationIntegral := prefixComparison.trans prefixBudget
  refine ⟨inputContinuous, forcingContinuous, observationContinuous, inputIntegrable, forcingIntegrable,
    observationIntegrable, prefixComparison, prefixBound, ?_⟩
  have cancellation : Real.exp (decay * start) * Real.exp (-decay * start) = 1 := by
    rw [← Real.exp_add, show decay * start + -decay * start = 0 by ring, Real.exp_zero]
  have sourceCancellation : Real.exp (decay * start) * sourceTerm / seed =
      (100 * constant / coefficient) * extent ^ 2 * magnitude / changed.ratio ^ 2 := by
    calc
      _ = (Real.exp (decay * start) * Real.exp (-decay * start)) * (seed / seed) *
          ((100 * constant / coefficient) * extent ^ 2 * magnitude / changed.ratio ^ 2) := by dsimp only [sourceTerm]; ring
      _ = _ := by rw [cancellation, div_self seedPositive.ne', one_mul, one_mul]
  have scaledPrefix := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left prefixBound (Real.exp_pos (decay * start)).le) seedPositive.le
  have combined := normalized.trans (add_le_add_left scaledPrefix coefficientTolerance)
  convert combined using 1
  rw [mul_add, add_div, sourceCancellation]
  dsimp only [observerCoefficient, observationIntegral]
  ring

end EulerNonuniqueness.Paper
