import EulerNonuniqueness.Section6.SourcePacketActualAdjacentPacketDiscrepancy
import EulerNonuniqueness.Section6.SourcePacketActualRetainedSignedCoefficient
import EulerNonuniqueness.Section5.Delay

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem retained_window_normalized_error {value coefficient prefixValue seed tolerance rate start tail : ℝ}
    (seedPositive : 0 < seed) (target : ℝ)
    (coefficientBound : |Real.exp (rate * start) * coefficient / seed - target| ≤
      tolerance / 2 + Real.exp (rate * start) * |prefixValue| / seed)
    (windowBound : |value - coefficient| ≤ Real.exp (-rate * start) *
      ((tolerance / 2) * seed + 17 * seed * tail)) :
    |Real.exp (rate * start) * value / seed - target| ≤
      tolerance + Real.exp (rate * start) * |prefixValue| / seed + 17 * tail := by
  have cancellation : Real.exp (rate * start) * Real.exp (-rate * start) = 1 := by
    rw [← Real.exp_add, show rate * start + -rate * start = 0 by ring, Real.exp_zero]
  have scaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left windowBound (Real.exp_pos (rate * start)).le) seedPositive.le
  have differenceBound : |Real.exp (rate * start) * value / seed -
      Real.exp (rate * start) * coefficient / seed| ≤ tolerance / 2 + 17 * tail := by
    rw [show Real.exp (rate * start) * value / seed - Real.exp (rate * start) * coefficient / seed =
      Real.exp (rate * start) * (value - coefficient) / seed by ring,
      abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos seedPositive]
    apply scaled.trans_eq
    rw [← mul_assoc, cancellation, one_mul]
    field_simp
    ring
  have triangle := abs_sub_le (Real.exp (rate * start) * value / seed)
    (Real.exp (rate * start) * coefficient / seed) target
  linarith only [triangle, differenceBound, coefficientBound]

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_actual_retained_signed_window :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ tolerance : ℝ, 0 < tolerance → tolerance ≤ 1 / 8 →
    ∀ scales : Scales, 0 < scales.amplitude → 0 < scales.alpha →
    max 2 (65536 / tolerance) ≤ scales.ratio →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime factor scaleRoot boundaryConstant radiusFactor initialError : ℝ),
    0 < factor → factor ≤ 1 / 8 → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < radiusFactor → initialError ≤ 1 / 64 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start ∈ Icc 0 path.stop, ∀ initialDistance outgoingPhase : ℝ,
    2048 ≤ initialDistance →
    initialDistance ≤ ({scales with frequency := frequency} : Scales).omega (source.val + 1) / 16 →
    12 * initialDistance ≤ (tolerance / 2) * scales.ratio →
    20 * initialError + 83200 / initialDistance ^ 2 ≤ min (tolerance / 4) 1 / 5120 →
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
    let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
    let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
    let windowCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
    let originalCoefficient := prefixIntegral + Real.exp (-decay * start) * windowCoefficient
    ContinuousOn input (Icc 0 path.stop) ∧ Continuous packet ∧
    IntegrableOn (fun elapsed => Real.exp (-decay * elapsed) * packet elapsed) (Ioi 0) ∧
    IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 start ∧
    windowCoefficient = seed * Real.cos residual +
      ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * rhombusConstantMomentInput positive initialMoment frozen elapsed ∧
    |windowCoefficient - seed * Real.cos residual| ≤ (tolerance / 2) * seed ∧
    |Real.exp (decay * start) * originalCoefficient / seed - Real.cos residual| ≤
      tolerance / 2 + Real.exp (decay * start) * |prefixIntegral| / seed ∧
    ∀ horizon : ℝ, 0 ≤ horizon → start + horizon ≤ path.stop →
      IntervalIntegrable (fun time => Real.exp (-decay * time) * input time) volume 0 (start + horizon) ∧
      IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed|) volume 0 horizon ∧
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * |input (start + elapsed) - packet elapsed|) ≤
        (tolerance / 2) * seed ∧
      |(∫ time in (0 : ℝ)..start + horizon, Real.exp (-decay * time) * input time) - originalCoefficient| ≤
        Real.exp (-decay * start) * ((tolerance / 2) * seed + 17 * seed * Real.exp (-(3 * decay / 4) * horizon)) ∧
      |Real.exp (decay * start) * (∫ time in (0 : ℝ)..start + horizon, Real.exp (-decay * time) * input time) / seed -
        Real.cos residual| ≤ tolerance + Real.exp (decay * start) * |prefixIntegral| / seed +
          17 * Real.exp (-(3 * decay / 4) * horizon) := by
  obtain ⟨radius, radiusPositive, radiusEighth, discrepancyFactory⟩ := exists_actual_adjacent_packet_discrepancy_budget
  refine ⟨radius, radiusPositive, radiusEighth, ?_⟩
  intro tolerance tolerancePositive toleranceEighth scales amplitudePositive alphaPositive ratioLarge referenceConstant
    referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime factor scaleRoot boundaryConstant
    radiusFactor initialError factorPositive factorSmall rootOne boundaryOne radiusFactorPositive initialErrorSmall
  have halfPositive : 0 < tolerance / 2 := by positivity
  have halfEighth : tolerance / 2 ≤ 1 / 8 := by linarith only [toleranceEighth]
  have halfOne : tolerance / 2 ≤ 1 := by linarith only [toleranceEighth]
  have ratioBound : 2 ≤ scales.ratio := (le_max_left _ _).trans ratioLarge
  have discrepancyRatio : max 2 (32768 / (tolerance / 2)) ≤ scales.ratio := by
    (convert ratioLarge using 1; congr 1; field_simp; ring)
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [discrepancyFactory (tolerance / 2) halfPositive halfOne scales amplitudePositive alphaPositive
      discrepancyRatio referenceConstant referenceNonnegative referenceAmplitude threshold thresholdBound orbit sectionTime
      factor scaleRoot boundaryConstant radiusFactor initialError factorPositive factorSmall rootOne boundaryOne
      radiusFactorPositive initialErrorSmall,
    eventually_actual_retained_signed_coefficient (tolerance / 2) halfPositive halfEighth scales amplitudePositive ratioBound
      alphaPositive orbit sectionTime (thresholdBound.trans radiusEighth) referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)] with frequency discrepancy retained frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start startInside initialDistance outgoingPhase
    initialLarge initialSmall ratioBudget numericBudget
  dsimp only
  intro firstInitial secondInitial initialProjection initialUpper prefixBounded
  have ratioNonnegative : 0 ≤ scales.ratio := by linarith only [ratioBound]
  have coarseRatio : 12 * initialDistance ≤ scales.ratio := ratioBudget.trans
    (mul_le_of_le_one_left ratioNonnegative halfOne)
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let omega := changed.omega (receiver.val + 1)
  let decay := 2 * Real.sqrt 2 * omega
  let seed := changed.seed (receiver.val + 1)
  let frozen : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let receiverPhase := phase (receiver.val + 1) - omega * start
  let residual := 4 * Complex.arg frozen - 2 * receiverPhase - 2 * outgoingPhase + Real.arctan (1 / Real.sqrt 2) - Real.pi
  let initialMoment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  let positive := fun elapsed : ℝ => Complex.exp (Complex.I * (receiverPhase - omega * elapsed : ℝ))
  let packet := fun elapsed => Real.cos residual * idealGrowingInput omega seed elapsed +
    Real.sin residual * idealQuadratureInput omega seed elapsed + rhombusConstantMomentInput positive initialMoment frozen elapsed
  let input := fun time => (relativeBlockSourceShapeInput changed motion reference receiver source time).1
  let prefixIntegral := ∫ time in (0 : ℝ)..start, Real.exp (-decay * time) * input time
  let windowCoefficient := ∫ elapsed in Ioi 0, Real.exp (-decay * elapsed) * packet elapsed
  let originalCoefficient := prefixIntegral + Real.exp (-decay * start) * windowCoefficient
  have lengthPositive := changed.length_pos (source.val + 1)
  have firstCoarse := firstInitial.trans (mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le)
  have secondCoarse := secondInitial.trans (mul_le_mul_of_nonneg_right initialErrorSmall lengthPositive.le)
  have actual := retained count phase dipoleAngle prepared path receiver source adjacent start startInside initialDistance outgoingPhase
    (by linarith only [initialLarge]) ratioBudget
    (by (convert firstCoarse using 1; ring)) (by (convert secondCoarse using 1; ring)) initialUpper
  dsimp only at actual
  obtain ⟨inputContinuous, packetContinuous, packetIntegrable, prefixIntegrable, coefficientIdentity,
    coefficientBound, normalizedBound, windowFactory⟩ := actual
  refine ⟨inputContinuous, packetContinuous, packetIntegrable, prefixIntegrable, coefficientIdentity,
    coefficientBound, normalizedBound, ?_⟩
  intro horizon horizonNonnegative endBound
  have numeric : 20 * initialError + 83200 / initialDistance ^ 2 ≤ min ((tolerance / 2) / 2) 1 / 5120 := by
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using numericBudget
  have absolute := discrepancy count phase dipoleAngle prepared path receiver source adjacent start horizon initialDistance outgoingPhase
    startInside.1 horizonNonnegative endBound initialLarge initialSmall coarseRatio numeric
    firstInitial secondInitial initialProjection initialUpper prefixBounded
  dsimp only at absolute
  obtain ⟨originalIntegrable, errorIntegrable, comparison⟩ := windowFactory horizon horizonNonnegative endBound
  have errorBound := absolute.2.2.2
  have finiteBound := comparison.trans (mul_le_mul_of_nonneg_left (add_le_add_right errorBound _)
    (Real.exp_pos (-decay * start)).le)
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive ratioPositive _
  exact ⟨originalIntegrable, errorIntegrable, errorBound, finiteBound,
    retained_window_normalized_error seedPositive (Real.cos residual) normalizedBound finiteBound⟩

end EulerNonuniqueness.Paper
