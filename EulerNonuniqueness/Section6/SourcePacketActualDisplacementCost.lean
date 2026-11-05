import EulerNonuniqueness.Section6.SourcePacketActualInheritedMoment
import EulerNonuniqueness.Section6.SourcePacketReceiverDisplacementFreezing
import EulerNonuniqueness.Section6.SourcePacketRetainedTargetMoment
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 3000000

private theorem weighted_displacement_cost {target error : ℝ → ℂ} {decay horizon distance tolerance seed : ℝ}
    (targetContinuous : Continuous target) (errorContinuous : Continuous error)
    (horizonNonnegative : 0 ≤ horizon) (distancePositive : 0 < distance) (toleranceNonnegative : 0 ≤ tolerance)
    (freeze : ∀ elapsed ∈ Icc 0 horizon, ‖error elapsed‖ ≤ tolerance * distance)
    (targetBound : (6 / (Real.pi * distance ^ 4)) *
      (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖target elapsed‖) ≤ 4 * seed) :
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) *
      (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * distance ^ 5))) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) *
      (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * distance ^ 5))) ≤ 512 * tolerance * seed := by
  have actualContinuous : Continuous (fun elapsed => Real.exp (-decay * elapsed) *
      (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * distance ^ 5))) := by fun_prop
  have majorantContinuous : Continuous (fun elapsed => (128 * tolerance * (6 / (Real.pi * distance ^ 4))) *
      (Real.exp (-decay * elapsed) * ‖target elapsed‖)) := by fun_prop
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      Real.exp (-decay * elapsed) * (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * distance ^ 5)) ≤
      (128 * tolerance * (6 / (Real.pi * distance ^ 4))) * (Real.exp (-decay * elapsed) * ‖target elapsed‖) := by
    have bound := mul_le_mul_of_nonneg_left (freeze elapsed inside)
      (show 0 ≤ Real.exp (-decay * elapsed) * 768 * ‖target elapsed‖ / (Real.pi * distance ^ 5) by positivity)
    convert bound using 1 <;> field_simp [distancePositive.ne', Real.pi_ne_zero] <;> ring
  have integrated := intervalIntegral.integral_mono_on (μ := volume) horizonNonnegative
    (actualContinuous.intervalIntegrable 0 horizon) (majorantContinuous.intervalIntegrable 0 horizon) pointwise
  rw [intervalIntegral.integral_const_mul] at integrated
  have scaled := mul_le_mul_of_nonneg_left targetBound (show 0 ≤ 128 * tolerance by positivity)
  refine ⟨actualContinuous.intervalIntegrable 0 horizon, integrated.trans ?_⟩
  convert scaled using 1 <;> ring

theorem Scales.eventually_actual_source_packet_displacement_cost (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {factor threshold scaleRoot boundaryConstant receiverRadiusFactor tolerance : ℝ}
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) (thresholdSmall : threshold ≤ 1 / 2)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (receiverRadiusPositive : 0 < receiverRadiusFactor) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {referenceConstant shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver ≠ source → ∀ patch : Fin 4,
    ∀ start horizon outgoingRadius outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    32 ≤ outgoingRadius → 12 * outgoingRadius ≤ scales.ratio → ∀ direction : ℂ, ‖direction‖ = 1 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let length : ℝ := changed.length (source.val + 1)
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * outgoingRadius →
    (∀ elapsed ∈ Icc 0 horizon, ‖patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) receiver‖ ≤
      receiverRadiusFactor * changed.length (receiver.val + 1)) →
    let displacement : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
    let moment := ∫ position, quadrupoleDensity changed motion start source position • (position - quadrupoleCenter motion start source) ^ 2
    let target := fun elapsed => moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed
    let error := fun elapsed => (patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - displacement
    IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * ‖displacement‖ ^ 5))) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      (768 * ‖target elapsed‖ * ‖error elapsed‖ / (Real.pi * ‖displacement‖ ^ 5))) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖displacement‖ ^ 4)) := by
  let freezeTolerance := min (1 / 2 : ℝ) (tolerance / 512)
  have freezePositive : 0 < freezeTolerance := by dsimp only [freezeTolerance]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (by linarith : 0 < scaleRoot) (by linarith : 0 ≤ boundaryConstant) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_source_packet_receiver_displacement_freezing amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall thresholdSmall rootOne boundaryOne receiverRadiusPositive freezePositive]
    with frequency frequencyOne inherited freezing
  intro count phase dipoleAngle referenceConstant shapeRadius monitor prepared path receiver source different patch
    start horizon outgoingRadius outgoingPhase startNonnegative horizonNonnegative endBound outgoingRadiusLarge ratioBudget direction directionNorm
  dsimp only
  intro firstInitial secondInitial centerBound ownRadius
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let displacement : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let moment := ∫ position, quadrupoleDensity changed motion start source position • (position - quadrupoleCenter motion start source) ^ 2
  let target := fun elapsed => moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed
  let error := fun elapsed => (patchCentroid motion (start + elapsed) receiver patch - quadrupoleCenter motion (start + elapsed) source) - displacement
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have distanceIdentity : ‖displacement‖ = |scales.location (receiver.val + 1) - scales.location (source.val + 1)| := by
    dsimp only [displacement]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rfl
  have distancePositive : 0 < ‖displacement‖ := by
    rw [distanceIdentity]
    exact scales.location_distance_pos (fun equality => different (Fin.ext (Nat.add_right_cancel equality)))
  have timeRange (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : start + elapsed ∈ Icc 0 path.stop :=
    ⟨by linarith [inside.1], by linarith [inside.2]⟩
  have actualInherited := inherited count phase dipoleAngle prepared path source start ⟨startNonnegative, by linarith⟩
    outgoingRadius outgoingRadiusLarge (by simpa only [one_mul] using ratioBudget) direction displacement directionNorm
    (norm_pos_iff.mp distancePositive) firstInitial secondInitial centerBound
  have targetBound := changed.retained_target_moment_weighted_bound source.val frequencyPositive ratioPositive moment
    outgoingPhase horizon ‖displacement‖ 1 horizonNonnegative distancePositive actualInherited
  have targetContinuous : Continuous target := by
    unfold target separatingLeadingMoment
    fun_prop
  have errorContinuous : Continuous error := by
    exact (((prepared.trajectory.movingFamily.patchCentroid_continuous receiver patch).sub
      (prepared.trajectory.movingFamily.quadrupoleCenter_continuous source)).comp
        (show Continuous (fun elapsed : ℝ => start + elapsed) from continuous_const.add continuous_id)).sub continuous_const
  have freeze (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : ‖error elapsed‖ ≤ freezeTolerance * ‖displacement‖ := by
    have actual := freezing count phase dipoleAngle prepared path (start + elapsed) (timeRange elapsed inside)
      receiver source different patch (ownRadius elapsed inside)
    simpa only [distanceIdentity] using actual
  have cost := weighted_displacement_cost (decay := 2 * Real.sqrt 2 * changed.omega source.val)
    (seed := Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖displacement‖ ^ 4))
    targetContinuous errorContinuous horizonNonnegative distancePositive freezePositive.le freeze (by
      norm_num only [show (1 : ℝ) + 3 = 4 by norm_num] at targetBound
      exact targetBound)
  have seedNonnegative : 0 ≤ Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
      (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖displacement‖ ^ 4) := by positivity
  refine ⟨cost.1, cost.2.trans ?_⟩
  have small : 512 * freezeTolerance ≤ tolerance := by
    have bound : freezeTolerance ≤ tolerance / 512 := min_le_right _ _
    linarith
  exact mul_le_mul_of_nonneg_right small seedNonnegative

end EulerNonuniqueness.Paper
