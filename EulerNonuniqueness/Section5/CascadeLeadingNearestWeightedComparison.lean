import EulerNonuniqueness.Section5.CascadeLeadingThreeWaySplit

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem weighted_first_projection_integral_le
    {function : ℝ → ℝ × ℝ} {weight finish : ℝ} (finishNonnegative : 0 ≤ finish)
    (scalarI : IntervalIntegrable (fun time => Real.exp (-weight * time) * (function time).1) volume 0 finish)
    (normI : IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖function time‖) volume 0 finish) :
    |∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (function time).1| ≤
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖function time‖ := by
  apply (intervalIntegral.abs_integral_le_integral_abs finishNonnegative).trans
  apply intervalIntegral.integral_mono_on finishNonnegative
    (by simpa only [Real.norm_eq_abs] using scalarI.norm) normI
  intro time _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Real.norm_eq_abs] using norm_fst_le (function time)) (Real.exp_pos _).le

theorem Scales.eventually_cascade_leading_nearest_weighted_comparison (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver adjacent : Fin count,
    receiver.val + 1 = adjacent.val →
    let changed : Scales := {scales with frequency := frequency}
    let input := fun source => relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source
    let leading := fun time => quadrupoleRelativeLeadingStrain changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference time receiver
    let coarser := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), input source time
    let older := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => adjacent.val < source.val), input source time
    ContinuousOn leading (Icc 0 path.stop) ∧ ContinuousOn coarser (Icc 0 path.stop) ∧
    ContinuousOn (input adjacent) (Icc 0 path.stop) ∧ ContinuousOn older (Icc 0 path.stop) ∧
    ∀ finish ∈ Icc 0 path.stop, ∀ weight : ℝ,
    let weightedFirst := fun function : ℝ → ℝ × ℝ =>
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (function time).1
    let weightedNorm := fun function : ℝ → ℝ × ℝ =>
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖function time‖
    (∀ function : ℝ → ℝ × ℝ,
      function = leading ∨ function = coarser ∨ function = input adjacent ∨ function = older →
      IntervalIntegrable (fun time => Real.exp (-weight * time) • function time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * (function time).1) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖function time‖) volume 0 finish) ∧
    |weightedFirst leading - weightedFirst (input adjacent)| ≤ weightedNorm coarser + weightedNorm older ∧
    ∀ origin tolerance seed : ℝ, 0 ≤ tolerance → 0 ≤ seed →
      Real.exp (weight * origin) * weightedNorm coarser ≤ tolerance * seed →
      Real.exp (weight * origin) * weightedNorm older ≤ tolerance * seed →
      Real.exp (weight * origin) * |weightedFirst leading - weightedFirst (input adjacent)| ≤ 2 * tolerance * seed := by
  filter_upwards [scales.eventually_cascade_leading_three_way_split amplitudePositive ratioBound alphaPositive orbit sectionTime
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall] with frequency split
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver adjacent next
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let input := fun source => relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
    prepared.reference receiver source
  let leading := fun time => quadrupoleRelativeLeadingStrain changed prepared.trajectory.movingFamily.patchMotion
    prepared.reference time receiver
  let coarser := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), input source time
  let older := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => adjacent.val < source.val), input source time
  obtain ⟨leadingContinuous, coarserContinuous, nearestContinuous, olderContinuous, identity⟩ :=
    split count phase dipoleAngle prepared path receiver adjacent next
  refine ⟨leadingContinuous, coarserContinuous, nearestContinuous, olderContinuous, ?_⟩
  intro finish finishInside weight
  let weightedFirst := fun function : ℝ → ℝ × ℝ =>
    ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (function time).1
  let weightedNorm := fun function : ℝ → ℝ × ℝ =>
    ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖function time‖
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishInside.2
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have integrable (function : ℝ → ℝ × ℝ) (regular : ContinuousOn function (Icc 0 path.stop)) :
      IntervalIntegrable (fun time => Real.exp (-weight * time) • function time) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * (function time).1) volume 0 finish ∧
      IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖function time‖) volume 0 finish := by
    exact ⟨(exponential.continuousOn.smul (regular.mono subset)).intervalIntegrable_of_Icc (μ := volume) finishInside.1,
      (exponential.continuousOn.mul ((regular.mono subset).fst)).intervalIntegrable_of_Icc (μ := volume) finishInside.1,
      (exponential.continuousOn.mul ((regular.mono subset).norm)).intervalIntegrable_of_Icc (μ := volume) finishInside.1⟩
  have leadingI := integrable leading leadingContinuous
  have coarserI := integrable coarser coarserContinuous
  have nearestI := integrable (input adjacent) nearestContinuous
  have olderI := integrable older olderContinuous
  have integralIdentity : weightedFirst leading = weightedFirst coarser + weightedFirst (input adjacent) + weightedFirst older := by
    have equality : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * (leading time).1) =
        ∫ time in (0 : ℝ)..finish, (Real.exp (-weight * time) * (coarser time).1 +
          Real.exp (-weight * time) * (input adjacent time).1) + Real.exp (-weight * time) * (older time).1 := by
      apply intervalIntegral.integral_congr
      intro time inside
      rw [uIcc_of_le finishInside.1] at inside
      have actual := identity time (subset inside)
      change leading time = coarser time + input adjacent time + older time at actual
      change Real.exp (-weight * time) * (leading time).1 =
        (Real.exp (-weight * time) * (coarser time).1 + Real.exp (-weight * time) * (input adjacent time).1) +
          Real.exp (-weight * time) * (older time).1
      rw [actual]
      simp only [Prod.fst_add]
      ring
    rw [intervalIntegral.integral_add (coarserI.2.1.add nearestI.2.1) olderI.2.1,
      intervalIntegral.integral_add coarserI.2.1 nearestI.2.1] at equality
    exact equality
  have coarserProjection := weighted_first_projection_integral_le finishInside.1 coarserI.2.1 coarserI.2.2
  have olderProjection := weighted_first_projection_integral_le finishInside.1 olderI.2.1 olderI.2.2
  have comparison : |weightedFirst leading - weightedFirst (input adjacent)| ≤ weightedNorm coarser + weightedNorm older := by
    calc
      _ = |weightedFirst coarser + weightedFirst older| := by rw [integralIdentity]; congr 1; ring
      _ ≤ |weightedFirst coarser| + |weightedFirst older| := abs_add _ _
      _ ≤ _ := add_le_add coarserProjection olderProjection
  refine ⟨?_, comparison, ?_⟩
  · intro function selected
    rcases selected with equal | equal | equal | equal
    · exact equal ▸ leadingI
    · exact equal ▸ coarserI
    · exact equal ▸ nearestI
    · exact equal ▸ olderI
  · intro origin tolerance seed _toleranceNonnegative _seedNonnegative coarserBound olderBound
    have scaled := mul_le_mul_of_nonneg_left comparison (Real.exp_pos (weight * origin)).le
    nlinarith only [scaled, coarserBound, olderBound]

end EulerNonuniqueness.Paper
