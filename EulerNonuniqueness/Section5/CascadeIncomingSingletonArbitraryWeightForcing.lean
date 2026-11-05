import EulerNonuniqueness.Section5.CascadeSelectedFinerExtentForcingRow
import EulerNonuniqueness.Section5.CascadeSelectedForeignForcingContinuity
import EulerNonuniqueness.Section6.UnstableDuhamel

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

private theorem incoming_profile_integral_bound {terminal finish rate weight amplitude : ℝ}
    (_finishNonnegative : 0 ≤ finish) (ratePositive : 0 < rate) (amplitudeNonnegative : 0 ≤ amplitude)
    (separated : 2 * weight ≤ rate) :
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (amplitude * Real.exp (rate * (time - terminal)))) ≤
      (2 * amplitude / rate) * Real.exp (-weight * terminal) *
        Real.exp ((rate - weight) * (finish - terminal)) := by
  have gapPositive : 0 < rate - weight := by linarith only [ratePositive, separated]
  let initial := amplitude * Real.exp (-rate * terminal)
  have initialNonnegative : 0 ≤ initial := mul_nonneg amplitudeNonnegative (Real.exp_pos _).le
  have bound := exponential_convolution_le (growth := rate - weight) (decay := 0)
    (time := finish) (amplitude := initial) (by simpa only [sub_zero] using gapPositive) initialNonnegative
  simp only [zero_mul, Real.exp_zero, one_mul, sub_zero] at bound
  have exponentialIdentity (time : ℝ) : Real.exp (-weight * time) * Real.exp (rate * (time - terminal)) =
      Real.exp (-rate * terminal) * Real.exp ((rate - weight) * time) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have integralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (amplitude * Real.exp (rate * (time - terminal)))) =
      ∫ time in (0 : ℝ)..finish, initial * Real.exp ((rate - weight) * time) := by
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only [initial]
    calc
      _ = amplitude * (Real.exp (-weight * time) * Real.exp (rate * (time - terminal))) := by ring
      _ = _ := by rw [exponentialIdentity]; ring
  have endpointIdentity : Real.exp (-rate * terminal) * Real.exp ((rate - weight) * finish) =
      Real.exp (-weight * terminal) * Real.exp ((rate - weight) * (finish - terminal)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have denominatorBound : rate / 2 ≤ rate - weight := by linarith only [separated]
  have comparison := div_le_div_of_nonneg_left
    (show 0 ≤ initial * Real.exp ((rate - weight) * finish) by positivity) (half_pos ratePositive) denominatorBound
  have productIdentity : initial * Real.exp ((rate - weight) * finish) =
      amplitude * (Real.exp (-weight * terminal) * Real.exp ((rate - weight) * (finish - terminal))) := by
    dsimp only [initial]
    rw [mul_assoc, endpointIdentity]
  rw [integralIdentity]
  apply bound.trans
  apply comparison.trans_eq
  rw [div_div_eq_mul_div, productIdentity]
  ring

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

theorem exists_uniform_actual_incoming_singleton_arbitrary_weight_forcing :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ), ∀ extent ≥ (1 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 100 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val < source.val →
    ∀ terminal coefficient magnitude weight : ℝ,
    0 ≤ terminal → terminal ≤ path.stop → 0 < coefficient → 0 ≤ magnitude → 0 ≤ weight →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ time ∈ Icc 0 terminal, ∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let sourceRate := coefficient * changed.omega (source.val + 1)
    let state := fun time => prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed first second source time‖ +
      ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let forcing := prepared.selectedForeignForcing {source} receiver
    let observation := fun time => ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ +
      ∑ patch : Fin 4, ‖patchCentroid first time receiver patch - patchCentroid second time receiver patch‖
    2 * weight ≤ sourceRate →
    (∀ time ∈ Icc 0 terminal, state time ≤ magnitude * Real.exp (sourceRate * (time - terminal))) →
    ContinuousOn forcing (Icc 0 terminal) ∧ ContinuousOn observation (Icc 0 terminal) ∧
    ∀ finish ∈ Icc 0 terminal,
      IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * observation time) volume 0 finish ∧
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) ≤
        (2 * constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 /
          (coefficient * changed.omega (source.val + 1) * gap ^ 4) *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * magnitude) *
            Real.exp (-weight * terminal) * Real.exp ((sourceRate - weight) * (finish - terminal)) +
        constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
          ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * observation time := by
  obtain ⟨rawCap, capPositive, constant, constantNonnegative, factory⟩ :=
    exists_uniform_actual_selected_finer_extent_forcing_row
  refine ⟨rawCap, capPositive, constant, constantNonnegative, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [factory extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_selected_foreign_forcing_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    eventually_gt_atTop (0 : ℝ)] with frequency estimates continuity frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered terminal coefficient magnitude weight
    terminalNonnegative terminalBound coefficientPositive magnitudeNonnegative _weightNonnegative referenceExtent alternativeExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let length := changed.length (source.val + 1)
  let sourceRate := coefficient * changed.omega (source.val + 1)
  let state := fun time => prepared.rawSourceCenteredState time source +
    ‖relativeNormalizedFirstMoment changed first second source time‖ +
    ‖quadrupoleCenter first time source - quadrupoleCenter second time source‖ / changed.location (source.val + 1) +
    ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let forcing := prepared.selectedForeignForcing {source} receiver
  let observation := fun time => ‖quadrupoleCenter first time receiver - quadrupoleCenter second time receiver‖ +
    ∑ patch : Fin 4, ‖patchCentroid first time receiver patch - patchCentroid second time receiver patch‖
  let strength := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
    (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1))
  let correction := constant * extent ^ 2 * changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5
  let amplitude := constant * extent ^ 2 * strength * magnitude
  let sourceUpper := fun time => amplitude * Real.exp (sourceRate * (time - terminal))
  intro separated profile
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have sourceRatePositive : 0 < sourceRate := mul_pos coefficientPositive (changed.omega_pos frequencyPositive ratioPositive _)
  have strengthNonnegative : 0 ≤ strength := by
    have circulationNonnegative := (changed.circulation_pos frequencyPositive ratioPositive (source.val + 1)).le
    have receiverPositive := changed.location_pos (receiver.val + 1)
    have sourcePositive := changed.location_pos (source.val + 1)
    dsimp only [strength]
    positivity
  have amplitudeNonnegative : 0 ≤ amplitude := by dsimp only [amplitude]; positivity
  have different : receiver ≠ source := fun equality => by simp only [equality, lt_self_iff_false] at ordered
  have selectedSubset : ({source} : Finset (Fin count)) ⊆ Finset.univ.erase receiver := by
    simpa only [Finset.singleton_subset_iff, Finset.mem_erase, Finset.mem_univ, and_true] using different.symm
  have forcingContinuous : ContinuousOn forcing (Icc 0 terminal) :=
    ((continuity count phase dipoleAngle prepared path receiver {source} selectedSubset).2.1).mono
      (Icc_subset_Icc le_rfl terminalBound)
  have referenceCenterContinuous : Continuous (fun time => quadrupoleCenter second time receiver) := by
    dsimp only [second]
    rw [prepared.referenceIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily.quadrupoleCenter_continuous receiver
  have referencePatchContinuous (patch : Fin 4) : Continuous (fun time => patchCentroid second time receiver patch) := by
    dsimp only [second]
    rw [prepared.referenceIdentity]
    exact prepared.referenceWitness.trajectory.movingFamily.patchCentroid_continuous receiver patch
  have observationContinuous : Continuous observation :=
    ((prepared.trajectory.movingFamily.quadrupoleCenter_continuous receiver).sub referenceCenterContinuous).norm.add
      (continuous_finset_sum _ fun patch _ =>
        ((prepared.trajectory.movingFamily.patchCentroid_continuous receiver patch).sub (referencePatchContinuous patch)).norm)
  have actualBound (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      forcing time ≤ sourceUpper time + correction * observation time := by
    have actual := (estimates count phase dipoleAngle prepared path time ⟨inside.1, inside.2.trans terminalBound⟩ receiver {source}
      (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact ordered)
      (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact referenceExtent time inside)
      (by intro current member; rcases Finset.mem_singleton.mp member with rfl; exact alternativeExtent time inside)).2.2.2
    dsimp only at actual
    simp only [Finset.sum_singleton] at actual
    have scaled := mul_le_mul_of_nonneg_left (profile time inside)
      (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg extent)) strengthNonnegative)
    calc
      forcing time ≤ constant * extent ^ 2 * strength * state time + correction * observation time := by
        convert actual using 1
        dsimp only [forcing, strength, state, correction, observation, first, second, gap, length, changed]
        ring
      _ ≤ sourceUpper time + correction * observation time := by
        convert add_le_add_right scaled (correction * observation time) using 1; dsimp only [sourceUpper, amplitude]; ring
  refine ⟨forcingContinuous, observationContinuous.continuousOn, ?_⟩
  intro finish inside
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 terminal := Icc_subset_Icc le_rfl inside.2
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have forcingIntegrable := (exponential.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc (μ := volume) inside.1
  have observationIntegrable := (exponential.mul observationContinuous).intervalIntegrable (μ := volume) 0 finish
  have sourceContinuous : Continuous sourceUpper := by fun_prop
  have sourceIntegrable := (exponential.mul sourceContinuous).intervalIntegrable (μ := volume) 0 finish
  have integrated := intervalIntegral.integral_mono_on inside.1 forcingIntegrable
    (sourceIntegrable.add (observationIntegrable.const_mul correction)) (by
      intro time member
      convert mul_le_mul_of_nonneg_left (actualBound time (subset member)) (Real.exp_pos (-weight * time)).le using 1; ring)
  rw [intervalIntegral.integral_add sourceIntegrable (observationIntegrable.const_mul correction),
    intervalIntegral.integral_const_mul] at integrated
  have sourceBound := incoming_profile_integral_bound (terminal := terminal) inside.1 sourceRatePositive amplitudeNonnegative separated
  refine ⟨forcingIntegrable, observationIntegrable, integrated.trans ?_⟩
  convert add_le_add_right sourceBound (correction * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * observation time) using 1
  dsimp only [sourceUpper, amplitude, strength, sourceRate, correction, gap, length, changed]
  ring

end EulerNonuniqueness.Paper
