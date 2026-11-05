import EulerNonuniqueness.Section5.CascadeExtentSourceLeadingReturn
import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section1.AdjacentIncomingPrefixPrefactor
import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_adjacent_extent_prefix :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ terminal coefficient magnitude : ℝ, 0 ≤ terminal → terminal ≤ path.stop → 0 < coefficient → 0 ≤ magnitude →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.reference
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let sourceRate := coefficient * changed.omega (source.val + 1)
    let state := fun time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed alternative reference source time‖ +
      ‖quadrupoleCenter alternative time source - quadrupoleCenter reference time source‖ /
        changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let input := relativeBlockSourceShapeInput changed alternative reference receiver source
    let receiverMotion := fun time => ‖quadrupoleCenter alternative time receiver - quadrupoleCenter reference time receiver‖
    weight ≤ sourceRate / 2 →
    (∀ time ∈ Icc 0 terminal, state time ≤ magnitude * Real.exp (sourceRate * (time - terminal))) →
    ContinuousOn input (Icc 0 terminal) ∧ ContinuousOn receiverMotion (Icc 0 terminal) ∧
    ∀ finish ∈ Icc 0 terminal,
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖input time‖) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * receiverMotion time) volume 0 finish ∧
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖input time‖) ≤
        (100 * (constant * extent ^ 2) / coefficient) * magnitude * (changed.seed (receiver.val + 1) / changed.ratio ^ 2) *
          Real.exp (-weight * terminal) * Real.exp ((sourceRate - weight) * (finish - terminal)) +
        (constant * extent ^ 2) * (changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5) *
          ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * receiverMotion time := by
  obtain ⟨rawCap, rawPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_extent_source_leading_return
  refine ⟨rawCap, rawPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [factory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ)] with frequency leadingEstimate inputContinuous frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent terminal coefficient magnitude
    terminalNonnegative terminalBound coefficientPositive magnitudeNonnegative firstExtent secondExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let length := changed.length (source.val + 1)
  let weight := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let sourceRate := coefficient * changed.omega (source.val + 1)
  let state := fun time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed alternative reference source time‖ +
    ‖quadrupoleCenter alternative time source - quadrupoleCenter reference time source‖ /
      changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let input := relativeBlockSourceShapeInput changed alternative reference receiver source
  let receiverMotion := fun time => ‖quadrupoleCenter alternative time receiver - quadrupoleCenter reference time receiver‖
  let strength := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
    (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1))
  let motionStrength := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5
  let scaledConstant := constant * extent ^ 2
  have scaledNonnegative : 0 ≤ scaledConstant := mul_nonneg constantNonnegative (sq_nonneg extent)
  let sourceUpper := fun time => scaledConstant * strength * magnitude * Real.exp (sourceRate * (time - terminal))
  intro rateSeparated profile
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have ordered : receiver.val < source.val := by omega
  have different : receiver ≠ source := fun same => by simp only [same, lt_self_iff_false] at ordered
  have adjacentIndex : source.val + 1 = (receiver.val + 1) + 1 := by omega
  have scalar := changed.adjacent_incoming_prefix_prefactor_le (receiver.val + 1) frequencyPositive ratioPositive
    coefficientPositive (by simpa only [← adjacentIndex] using rateSeparated)
  simp only [← adjacentIndex] at scalar
  change 0 < sourceRate - weight ∧ strength / (sourceRate - weight) ≤
    (100 / coefficient) * changed.seed (receiver.val + 1) / changed.ratio ^ 2 at scalar
  have strengthNonnegative : 0 ≤ strength := by
    have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have receiverPositive := changed.location_pos (receiver.val + 1)
    have sourcePositive := changed.location_pos (source.val + 1)
    dsimp only [strength]
    positivity
  have actualInputContinuous : ContinuousOn input (Icc 0 terminal) :=
    (inputContinuous count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path receiver source different).mono
      (Icc_subset_Icc le_rfl terminalBound)
  have referenceCenterContinuous : Continuous (fun time => quadrupoleCenter reference time receiver) := by
    dsimp only [reference]
    rw [prepared.referenceIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily.quadrupoleCenter_continuous receiver
  have receiverMotionContinuous : Continuous receiverMotion :=
    ((prepared.trajectory.movingFamily.quadrupoleCenter_continuous receiver).sub referenceCenterContinuous).norm
  have sourceUpperContinuous : Continuous sourceUpper := by fun_prop
  have actualBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      ‖input time‖ ≤ sourceUpper time + scaledConstant * motionStrength * receiverMotion time := by
    have actual := (leadingEstimate count phase dipoleAngle prepared path receiver source ordered time
      ⟨inside.1, inside.2.trans terminalBound⟩ (firstExtent time inside) (secondExtent time inside)).2
    change ‖input time‖ ≤ scaledConstant * (strength * state time + motionStrength * receiverMotion time) at actual
    have scaled := mul_le_mul_of_nonneg_left (profile time inside) (mul_nonneg scaledNonnegative strengthNonnegative)
    calc
      ‖input time‖ ≤ scaledConstant * strength * state time + scaledConstant * motionStrength * receiverMotion time := by
        convert actual using 1; ring
      _ ≤ sourceUpper time + scaledConstant * motionStrength * receiverMotion time := by
        convert add_le_add_right scaled (scaledConstant * motionStrength * receiverMotion time) using 1; ring
  refine ⟨actualInputContinuous, receiverMotionContinuous.continuousOn, ?_⟩
  intro finish inside
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 terminal := Icc_subset_Icc le_rfl inside.2
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have inputIntegrable := (weightContinuous.continuousOn.mul (actualInputContinuous.norm.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have receiverIntegrable := (weightContinuous.mul receiverMotionContinuous).intervalIntegrable (μ := volume) 0 finish
  have sourceIntegrable := (weightContinuous.mul sourceUpperContinuous).intervalIntegrable (μ := volume) 0 finish
  have majorantIntegrable := sourceIntegrable.add (receiverIntegrable.const_mul (scaledConstant * motionStrength))
  have integrated := intervalIntegral.integral_mono_on inside.1 inputIntegrable majorantIntegrable (by
    intro time member
    have scaled := mul_le_mul_of_nonneg_left (actualBound time (subset member)) (Real.exp_pos (-weight * time)).le
    convert scaled using 1; ring)
  rw [intervalIntegral.integral_add sourceIntegrable (receiverIntegrable.const_mul (scaledConstant * motionStrength)),
    intervalIntegral.integral_const_mul] at integrated
  let amplitude := scaledConstant * strength * magnitude * Real.exp (-sourceRate * terminal)
  have amplitudeNonnegative : 0 ≤ amplitude := by dsimp only [amplitude]; positivity
  have convolution := exponential_convolution_le (growth := sourceRate - weight) (decay := 0)
    (time := finish) (amplitude := amplitude) (by simpa only [sub_zero] using scalar.1) amplitudeNonnegative
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero] at convolution
  have integrandIdentity (time : ℝ) : Real.exp (-weight * time) * sourceUpper time =
      amplitude * Real.exp ((sourceRate - weight) * time) := by
    dsimp only [sourceUpper, amplitude]
    have exponential : Real.exp (-weight * time) * Real.exp (sourceRate * (time - terminal)) =
        Real.exp (-sourceRate * terminal) * Real.exp ((sourceRate - weight) * time) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      _ = (scaledConstant * strength * magnitude) *
          (Real.exp (-weight * time) * Real.exp (sourceRate * (time - terminal))) := by ring
      _ = _ := by rw [exponential]; ring
  have originalIntegralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * sourceUpper time) =
      ∫ time in (0 : ℝ)..finish, amplitude * Real.exp ((sourceRate - weight) * time) := by
    apply intervalIntegral.integral_congr
    intro time _
    exact integrandIdentity time
  have endpointExponential : Real.exp (-sourceRate * terminal) * Real.exp ((sourceRate - weight) * finish) =
      Real.exp (-weight * terminal) * Real.exp ((sourceRate - weight) * (finish - terminal)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have profileIntegralBound : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * sourceUpper time) ≤
      (100 * (scaledConstant) / coefficient) * magnitude * (changed.seed (receiver.val + 1) / changed.ratio ^ 2) *
        Real.exp (-weight * terminal) * Real.exp ((sourceRate - weight) * (finish - terminal)) := by
    rw [originalIntegralIdentity]
    apply convolution.trans
    have scaled := mul_le_mul_of_nonneg_left scalar.2
      (show 0 ≤ scaledConstant * magnitude * (Real.exp (-weight * terminal) *
        Real.exp ((sourceRate - weight) * (finish - terminal))) by positivity)
    calc
      amplitude * Real.exp ((sourceRate - weight) * finish) / (sourceRate - weight) =
          scaledConstant * magnitude * (Real.exp (-weight * terminal) *
            Real.exp ((sourceRate - weight) * (finish - terminal))) * (strength / (sourceRate - weight)) := by
        dsimp only [amplitude]
        rw [mul_assoc (scaledConstant * strength * magnitude), endpointExponential]
        ring
      _ ≤ _ := by convert scaled using 1; ring
  exact ⟨inputIntegrable, receiverIntegrable, integrated.trans (add_le_add_right profileIntegralBound _)⟩

end EulerNonuniqueness.Paper

