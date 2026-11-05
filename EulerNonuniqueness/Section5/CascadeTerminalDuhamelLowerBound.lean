import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel
import EulerNonuniqueness.Section5.CascadeLeadingThreeWaySplit

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

private theorem weighted_first_component_lower
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

theorem exists_uniform_actual_terminal_duhamel_lower_bound
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
    receiver.val + 1 = source.val → source.val + 1 = count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time receiver| +
        |stableShape (cascadePairedMotion prepared side) time receiver| < radius) →
    let changed : Scales := {scales with frequency := frequency}
    let motion := prepared.trajectory.movingFamily.patchMotion
    let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
    let seed := changed.seed (receiver.val + 1)
    let nearest := relativeBlockSourceShapeInput changed motion prepared.reference receiver source
    let coarser := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => current.val < receiver.val),
      relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
    let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate receiver
    (3 * seed / 4 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (nearest time).1) →
    ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖coarser time‖) ≤ seed / 8) →
    ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖remainder time‖) ≤ seed / 8) →
    seed * Real.exp (growth * finish) / 2 ≤
      (referenceStraightenedShape motion graph coordinate receiver finish -
        referenceStraightenedShape prepared.reference graph coordinate receiver finish).1 := by
  obtain ⟨radius, radiusPositive, radiusQuarter, duhamel⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [scales.eventually_cascade_leading_three_way_split amplitudePositive ratioBound alphaPositive
    orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall] with frequency splitting
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source adjacent terminal
    finish finishNonnegative finishBound small
  dsimp only
  intro nearestLower coarserSmall remainderSmall
  let changed : Scales := {scales with frequency := frequency}
  let motion := prepared.trajectory.movingFamily.patchMotion
  let growth := 2 * Real.sqrt 2 * changed.omega (receiver.val + 1)
  let seed := changed.seed (receiver.val + 1)
  let nearest := relativeBlockSourceShapeInput changed motion prepared.reference receiver source
  let coarser := fun time => ∑ current ∈ Finset.univ.filter (fun current : Fin count => current.val < receiver.val),
    relativeBlockSourceShapeInput changed motion prepared.reference receiver current time
  let leading := fun time => quadrupoleRelativeLeadingStrain changed motion prepared.reference time receiver
  let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate receiver
  let input := fun time => leading time + remainder time
  let relative := fun time => referenceStraightenedShape motion graph coordinate receiver time -
    referenceStraightenedShape prepared.reference graph coordinate receiver time
  have nonterminal : receiver.val + 1 < count := by omega
  obtain ⟨leadingContinuous, coarserContinuous, nearestContinuous, _, leadingSplit⟩ :=
    splitting count phase dipoleAngle prepared path receiver source adjacent
  have olderEmpty : Finset.univ.filter (fun current : Fin count => source.val < current.val) = ∅ := by
    ext current
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.not_mem_empty, iff_false]
    omega
  have exactSplit (time : ℝ) (inside : time ∈ Icc 0 finish) : leading time = coarser time + nearest time := by
    have actual := leadingSplit time ⟨inside.1, inside.2.trans finishBound⟩
    simpa only [olderEmpty, Finset.sum_empty, add_zero] using actual
  obtain ⟨inputContinuous, unstableIdentity, _, _, _⟩ :=
    duhamel prepared path receiver nonterminal finish finishNonnegative finishBound small
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have coarseC : ContinuousOn coarser (Icc 0 finish) := coarserContinuous.mono subset
  have nearestC : ContinuousOn nearest (Icc 0 finish) := nearestContinuous.mono subset
  have remainderC : ContinuousOn remainder (Icc 0 finish) := by
    have candidate := inputContinuous.sub (leadingContinuous.mono subset)
    apply candidate.congr
    intro time _
    change remainder time = leading time + remainder time - leading time
    abel
  have kernel : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have coarseFirstI := (kernel.continuousOn.mul coarseC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have nearestFirstI := (kernel.continuousOn.mul nearestC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have remainderFirstI := (kernel.continuousOn.mul remainderC.fst).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have inputSplit (time : ℝ) (inside : time ∈ Icc 0 finish) :
      (input time).1 = (coarser time).1 + (nearest time).1 + (remainder time).1 := by
    dsimp only [input]
    rw [exactSplit time inside]
    rfl
  have integralSplit : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) =
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (coarser time).1) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (nearest time).1) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (remainder time).1) := by
    have equality : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1) =
        ∫ time in (0 : ℝ)..finish,
          Real.exp (-growth * time) * (coarser time).1 + Real.exp (-growth * time) * (nearest time).1 +
            Real.exp (-growth * time) * (remainder time).1 := by
      apply intervalIntegral.integral_congr
      intro time inside
      rw [uIcc_of_le finishNonnegative] at inside
      dsimp only
      rw [inputSplit time inside]
      ring
    rw [equality, intervalIntegral.integral_add (coarseFirstI.add nearestFirstI) remainderFirstI,
      intervalIntegral.integral_add coarseFirstI nearestFirstI]
  have coarseLower := weighted_first_component_lower (weight := growth) coarseC finishNonnegative
  have remainderLower := weighted_first_component_lower (weight := growth) remainderC finishNonnegative
  have normalizedLower : seed / 2 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (input time).1 := by
    rw [integralSplit]
    linarith only [coarseLower, remainderLower, nearestLower, coarserSmall, remainderSmall]
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
  rw [response]
  have scaled := mul_le_mul_of_nonneg_left normalizedLower (Real.exp_pos (growth * finish)).le
  convert scaled using 1
  ring

end EulerNonuniqueness.Paper
