import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel
import EulerNonuniqueness.Section5.CascadeLeadingThreeWaySplit
import EulerNonuniqueness.Section5.Delay

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem incoming_weighted_first_component_lower
    {function : ℝ → ℝ × ℝ} {finish weight : ℝ}
    (regular : ContinuousOn function (Icc 0 finish)) (finishNonnegative : 0 ≤ finish) :
    -(∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖function time‖) ≤
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (function time).1 := by
  have kernel : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have normI := (kernel.continuousOn.mul regular.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have firstI := (kernel.continuousOn.mul regular.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have compared := intervalIntegral.integral_mono_on finishNonnegative normI.neg firstI (by
    intro time _
    have component : |(function time).1| ≤ ‖function time‖ := by
      simpa only [Real.norm_eq_abs] using norm_fst_le (function time)
    have lower : -‖function time‖ ≤ (function time).1 := by
      linarith only [component, neg_abs_le (function time).1]
    have scaled := mul_le_mul_of_nonneg_left lower (Real.exp_pos (-weight * time)).le
    simpa only [mul_neg] using scaled)
  simpa only [Pi.neg_apply, intervalIntegral.integral_neg] using compared

theorem exists_uniform_actual_incoming_duhamel_lower_bound
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ (orbit : SeparatingOrbit) (sectionTime : ℝ),
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver source : Fin count,
    receiver.val + 1 = source.val →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time receiver| +
        |stableShape (cascadePairedMotion prepared side) time receiver| < radius) →
    ∀ origin : ℝ,
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let nearest := relativeBlockSourceShapeInput changed motion prepared.reference receiver source
    let coarser := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => current.val < receiver.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
    let older := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => source.val < current.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
    let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate receiver
    (3 * seed / 4 ≤ Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (nearest time).1)) →
    (Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖coarser time‖) ≤ seed / 16) →
    (Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖older time‖) ≤ seed / 16) →
    (Real.exp (growth * origin) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖remainder time‖) ≤ seed / 16) →
    seed * Real.exp (growth * (finish - origin)) / 2 ≤
      (referenceStraightenedShape motion graph coordinate receiver finish -
        referenceStraightenedShape prepared.reference graph coordinate receiver finish).1 := by
  obtain ⟨radius, radiusPositive, radiusQuarter, duhamel⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [scales.eventually_cascade_leading_three_way_split amplitudePositive ratioBound alphaPositive
    orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ)] with frequency splitting frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent
    finish finishNonnegative finishBound small origin
  dsimp only
  intro nearestLower coarserSmall olderSmall remainderSmall
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let nearest := relativeBlockSourceShapeInput changed motion prepared.reference receiver source
  let coarser := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => current.val < receiver.val),
    relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
  let older := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => source.val < current.val),
    relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
  let leading := fun time => quadrupoleRelativeLeadingStrain changed motion prepared.reference time receiver
  let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate receiver
  let input := fun time => leading time + remainder time
  let relative := fun time => referenceStraightenedShape motion graph coordinate receiver time -
    referenceStraightenedShape prepared.reference graph coordinate receiver time
  have nonterminal : receiver.val + 1 < count := by omega
  obtain ⟨leadingContinuous, coarserContinuous, nearestContinuous, olderContinuous, leadingSplit⟩ :=
    splitting count phase dipoleAngle prepared path receiver source adjacent
  have exactSplit (time : ℝ) (inside : time ∈ Icc 0 finish) : leading time = coarser time + nearest time + older time :=
    leadingSplit time ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨inputContinuous, unstableIdentity, _, _, _⟩ :=
    duhamel prepared path receiver nonterminal finish finishNonnegative finishBound small
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have coarseC : ContinuousOn coarser (Icc 0 finish) := coarserContinuous.mono subset
  have nearestC : ContinuousOn nearest (Icc 0 finish) := nearestContinuous.mono subset
  have olderC : ContinuousOn older (Icc 0 finish) := olderContinuous.mono subset
  have remainderC : ContinuousOn remainder (Icc 0 finish) := by
    have candidate := inputContinuous.sub (leadingContinuous.mono subset)
    apply candidate.congr
    intro time _
    change remainder time = leading time + remainder time - leading time
    abel
  have kernel : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have coarseFirstI := (kernel.continuousOn.mul coarseC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have nearestFirstI := (kernel.continuousOn.mul nearestC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have olderFirstI := (kernel.continuousOn.mul olderC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have remainderFirstI := (kernel.continuousOn.mul remainderC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have inputSplit (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (input time).1 = (coarser time).1 + (nearest time).1 + (older time).1 + (remainder time).1 := by
    dsimp only [input]
    rw [exactSplit time inside]
    rfl
  have integralSplit : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) =
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (coarser time).1) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (nearest time).1) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (older time).1) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (remainder time).1) := by
    have equality : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) =
        ∫ time in (0 : ℝ)..finish,
          Real.exp (-growth * time) * (coarser time).1 + Real.exp (-growth * time) * (nearest time).1 +
            Real.exp (-growth * time) * (older time).1 + Real.exp (-growth * time) * (remainder time).1 := by
      apply intervalIntegral.integral_congr
      intro time inside
      rw [uIcc_of_le finishNonnegative] at inside
      dsimp only
      rw [inputSplit time inside]
      ring
    rw [equality, intervalIntegral.integral_add ((coarseFirstI.add nearestFirstI).add olderFirstI) remainderFirstI,
      intervalIntegral.integral_add (coarseFirstI.add nearestFirstI) olderFirstI,
      intervalIntegral.integral_add coarseFirstI nearestFirstI]
  have coarseLower := incoming_weighted_first_component_lower (weight := growth) coarseC finishNonnegative
  have olderLower := incoming_weighted_first_component_lower (weight := growth) olderC finishNonnegative
  have remainderLower := incoming_weighted_first_component_lower (weight := growth) remainderC finishNonnegative
  have coarseScaled := mul_le_mul_of_nonneg_left coarseLower (Real.exp_pos (growth * origin)).le
  have olderScaled := mul_le_mul_of_nonneg_left olderLower (Real.exp_pos (growth * origin)).le
  have remainderScaled := mul_le_mul_of_nonneg_left remainderLower (Real.exp_pos (growth * origin)).le
  have seedPositive : 0 < seed := changed.seed_pos frequencyPositive
    (by change 0 < scales.ratio; linarith only [ratioBound]) _
  have normalizedLower : seed / 2 ≤ Real.exp (growth * origin) *
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) := by
    rw [integralSplit]
    nlinarith only [coarseScaled, olderScaled, remainderScaled, nearestLower, coarserSmall, olderSmall, remainderSmall, seedPositive]
  have response : (relative finish).1 = Real.exp (growth * finish) *
      ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1 := by
    have identity := unstableIdentity finish ⟨finishNonnegative, le_rfl⟩
    change (relative finish).1 = ∫ time in (0 : ℝ)..finish, Real.exp (growth * (finish - time)) * (input time).1 at identity
    rw [identity, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro time _
    dsimp only
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  change seed * Real.exp (growth * (finish - origin)) / 2 ≤ (relative finish).1
  rw [response]
  have exponentialIdentity : Real.exp (growth * (finish - origin)) * Real.exp (growth * origin) =
      Real.exp (growth * finish) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have scaled := mul_le_mul_of_nonneg_left normalizedLower (Real.exp_pos (growth * (finish - origin))).le
  calc
    seed * Real.exp (growth * (finish - origin)) / 2 = Real.exp (growth * (finish - origin)) * (seed / 2) := by ring
    _ ≤ Real.exp (growth * (finish - origin)) * (Real.exp (growth * origin) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1)) := scaled
    _ = Real.exp (growth * finish) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) := by
      rw [← mul_assoc, exponentialIdentity]

end EulerNonuniqueness.Paper
