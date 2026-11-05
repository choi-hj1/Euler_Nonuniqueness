import EulerNonuniqueness.Section6.SourcePacketReferenceRecipient
import EulerNonuniqueness.Section6.SourcePacketPhysicalComparison

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem source_packet_weighted_uniform_orientation_cost
    {target orientation : ℝ → ℂ} {decay horizon coefficient tolerance budget : ℝ}
    (targetContinuous : Continuous target) (orientationMeasurable : Measurable orientation)
    (horizonNonnegative : 0 ≤ horizon) (coefficientNonnegative : 0 ≤ coefficient) (toleranceNonnegative : 0 ≤ tolerance)
    (orientationBound : ∀ elapsed ∈ Icc 0 horizon, ‖orientation elapsed‖ ≤ tolerance)
    (targetBound : coefficient * (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * ‖target elapsed‖) ≤ budget) :
    IntervalIntegrable (fun elapsed => Real.exp (-decay * elapsed) * (coefficient * ‖target elapsed‖ * ‖orientation elapsed‖))
      volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-decay * elapsed) * (coefficient * ‖target elapsed‖ * ‖orientation elapsed‖)) ≤
      tolerance * budget := by
  have measurable : Measurable (fun elapsed => Real.exp (-decay * elapsed) * (coefficient * ‖target elapsed‖ * ‖orientation elapsed‖)) :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
      ((measurable_const.mul targetContinuous.measurable.norm).mul orientationMeasurable.norm)
  have majorant : Continuous (fun elapsed : ℝ => (tolerance * coefficient) * (Real.exp (-decay * elapsed) * ‖target elapsed‖)) := by fun_prop
  have pointwise (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) :
      ‖Real.exp (-decay * elapsed) * (coefficient * ‖target elapsed‖ * ‖orientation elapsed‖)‖ ≤
        (tolerance * coefficient) * (Real.exp (-decay * elapsed) * ‖target elapsed‖) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have bound := mul_le_mul_of_nonneg_left (orientationBound elapsed inside)
      (show 0 ≤ Real.exp (-decay * elapsed) * coefficient * ‖target elapsed‖ by positivity)
    convert bound using 1 <;> ring
  have integrable := (majorant.intervalIntegrable (μ := volume) 0 horizon).mono_fun' measurable.aestronglyMeasurable.restrict (by
    rw [uIoc_of_le horizonNonnegative]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with elapsed inside
    exact pointwise elapsed ⟨inside.1.le, inside.2⟩)
  refine ⟨integrable, ?_⟩
  have integrated := intervalIntegral.integral_mono_on horizonNonnegative integrable
    (majorant.intervalIntegrable 0 horizon) (fun elapsed inside => (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using pointwise elapsed inside))
  rw [intervalIntegral.integral_const_mul] at integrated
  have scaled := mul_le_mul_of_nonneg_left targetBound toleranceNonnegative
  exact integrated.trans (by convert scaled using 1 <;> ring)

set_option maxHeartbeats 3000000

theorem exists_source_packet_reference_frame_phase_cost :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 8 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ referenceConstant ≥ (0 : ℝ), referenceConstant ≤ scales.amplitude → ∀ threshold ≤ radius,
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ) (factor scaleRoot boundaryConstant tolerance : ℝ),
    0 < factor → factor ≤ 1 → 0 < scaleRoot → 0 ≤ boundaryConstant → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ}
      (prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count),
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count, receiver.val + 1 = source.val →
    ∀ start horizon outgoingRadius outgoingPhase : ℝ, 0 ≤ start → 0 ≤ horizon → start + horizon ≤ path.stop →
    32 ≤ outgoingRadius → 12 * outgoingRadius ≤ scales.ratio →
    ∀ direction displacement : ℂ, ‖direction‖ = 1 → displacement ≠ 0 →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
    let length := changed.length (source.val + 1)
    let positive := fun elapsed => positiveHalfDiagonal reference (start + elapsed) receiver
    let ideal := fun elapsed => Complex.exp (Complex.I *
      ((phase (receiver.val + 1) - changed.omega source.val * (start + elapsed) : ℝ) : ℂ))
    ‖firstDipoleSeparation motion start source - (length : ℂ) * direction‖ ≤ length / 64 →
    ‖secondDipoleSeparation motion start source - (length : ℂ) * (-direction)‖ ≤ length / 64 →
    ‖firstDipoleCenter motion start source - secondDipoleCenter motion start source‖ ≤ (5 / 4 : ℝ) * length * outgoingRadius →
    let moment := ∫ position, quadrupoleDensity changed motion start source position •
      (position - quadrupoleCenter motion start source) ^ 2
    IntervalIntegrable (fun elapsed => Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      ((6 / (Real.pi * ‖displacement‖ ^ 4)) *
        ‖moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed‖ *
        ‖star (positive elapsed) / positive elapsed - star (ideal elapsed) / ideal elapsed‖)) volume 0 horizon ∧
    (∫ elapsed in (0 : ℝ)..horizon, Real.exp (-(2 * Real.sqrt 2 * changed.omega source.val) * elapsed) *
      ((6 / (Real.pi * ‖displacement‖ ^ 4)) *
        ‖moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed‖ *
        ‖star (positive elapsed) / positive elapsed - star (ideal elapsed) / ideal elapsed‖)) ≤
      tolerance * (Real.sqrt 3 * changed.circulation (source.val + 1) ^ 2 /
        (2 * Real.sqrt 2 * Real.pi ^ 2 * changed.omega source.val ^ 2 * ‖displacement‖ ^ 4)) := by
  obtain ⟨radius, radiusPositive, radiusSmall, recipient⟩ := exists_source_packet_reference_recipient
  refine ⟨radius, radiusPositive, radiusSmall, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
    orbit sectionTime factor scaleRoot boundaryConstant tolerance factorPositive factorSmall rootPositive boundaryNonnegative tolerancePositive
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    recipient scales amplitudePositive ratioBound alphaPositive referenceConstant referenceNonnegative amplitudeBound threshold thresholdBound
      1 (tolerance / 4) (by norm_num) (by positivity),
    scales.eventually_actual_inherited_moment_arbitrary_budget amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall rootPositive boundaryNonnegative (by norm_num : (0 : ℝ) < 1)]
    with frequency frequencyOne recipient inherited
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent start horizon outgoingRadius outgoingPhase
    startNonnegative horizonNonnegative endBound outgoingLarge ratioBudget direction displacement directionNorm displacementNonzero
  dsimp only
  intro firstInitial secondInitial centerBound
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let positive := fun elapsed => positiveHalfDiagonal reference (start + elapsed) receiver
  let ideal := fun elapsed => Complex.exp (Complex.I *
    ((phase (receiver.val + 1) - changed.omega source.val * (start + elapsed) : ℝ) : ℂ))
  let orientation := fun elapsed => star (positive elapsed) / positive elapsed - star (ideal elapsed) / ideal elapsed
  let moment := ∫ position, quadrupoleDensity changed motion start source position •
    (position - quadrupoleCenter motion start source) ^ 2
  let target := fun elapsed => moment + separatingLeadingMoment (changed.circulation (source.val + 1)) outgoingPhase elapsed
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have positiveContinuous : Continuous positive :=
    (((prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 0).sub
      (prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver 1)).div_const 2).comp
      (continuous_const.add continuous_id)
  have idealContinuous : Continuous ideal := by dsimp only [ideal]; fun_prop
  have orientationMeasurable : Measurable orientation :=
    ((measurable_complex_star positiveContinuous.measurable).div positiveContinuous.measurable).sub
      ((measurable_complex_star idealContinuous.measurable).div idealContinuous.measurable)
  have targetContinuous : Continuous target := by dsimp only [target]; unfold separatingLeadingMoment; fun_prop
  have orientationBound (elapsed : ℝ) (inside : elapsed ∈ Icc 0 horizon) : ‖orientation elapsed‖ ≤ tolerance / 4 := by
    have timeInside : start + elapsed ∈ Icc (0 : ℝ) 1 := ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
    have actual := (recipient prepared.referenceWitness (start + elapsed) timeInside receiver).2.2.2
    simpa only [orientation, positive, ideal, adjacent] using actual
  have startInside : start ∈ Icc 0 path.stop := ⟨startNonnegative, by linarith⟩
  have inheritedBound := inherited count phase dipoleAngle prepared path source start startInside outgoingRadius outgoingLarge
    (by simpa using ratioBudget) direction displacement directionNorm displacementNonzero firstInitial secondInitial centerBound
  simp only [one_mul] at inheritedBound
  have targetBound := changed.retained_target_moment_weighted_bound source.val frequencyPositive ratioPositive moment outgoingPhase
    horizon ‖displacement‖ 1 horizonNonnegative (norm_pos_iff.mpr displacementNonzero) (by simpa only [one_mul] using inheritedBound)
  norm_num only at targetBound
  obtain ⟨integrable, bound⟩ := source_packet_weighted_uniform_orientation_cost targetContinuous orientationMeasurable
    horizonNonnegative (show 0 ≤ 6 / (Real.pi * ‖displacement‖ ^ 4) by positivity)
    (show 0 ≤ tolerance / 4 by positivity) orientationBound targetBound
  refine ⟨integrable, ?_⟩
  convert bound using 1 <;> ring

end EulerNonuniqueness.Paper
