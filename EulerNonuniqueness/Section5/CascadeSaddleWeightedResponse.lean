import EulerNonuniqueness.Section5.CascadeSaddleOriginalDuhamel

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_saddle_weighted_response
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ} {phase dipoleAngle : ℕ → ℝ}
      {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ},
    0 < scales.frequency → 0 < scales.ratio →
    ∀ prepared : CascadeMaterialPreparedPair scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ side, ∀ time ∈ Icc 0 finish,
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < radius) →
    let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time
    let leading := fun time => quadrupoleRelativeLeadingStrain scales prepared.trajectory.movingFamily.patchMotion
      prepared.reference time index
    let remainder := relativeStraightenedSaddleStrainRemainder scales (cascadePairedMotion prepared) graph coordinate index
    let growth := 2 * Real.sqrt 2 * scales.omega (index.val + 1)
    0 < growth ∧
    ContinuousOn (fun time => leading time + remainder time) (Icc 0 finish) ∧
    (∀ time ∈ Icc 0 finish,
      Real.exp (-growth * time) * (relative time).1 =
        ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current + remainder current).1) ∧
    growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
      (1 / 2 : ℝ) * (∫ time in (0 : ℝ)..finish,
        Real.exp (-growth * time) * |(leading time + remainder time).2|) ∧
    (∀ time : ℝ,
      |(leading time + remainder time).1| ≤ |(leading time).1| + ‖remainder time‖ ∧
      |(leading time + remainder time).2| ≤ |(leading time).2| + ‖remainder time‖) := by
  obtain ⟨radius, radiusPositive, radiusQuarter, factory⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  refine ⟨radius, radiusPositive, radiusQuarter, ?_⟩
  intro scales orbit sectionTime phase dipoleAngle threshold referenceConstant scaleRoot shapeRadius factor monitor
    boundaryConstant count frequencyPositive ratioPositive prepared path index nonterminal finish finishNonnegative finishBound small
  let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
    referenceStraightenedShape prepared.reference graph coordinate index time
  let leading := fun time => quadrupoleRelativeLeadingStrain scales prepared.trajectory.movingFamily.patchMotion
    prepared.reference time index
  let remainder := relativeStraightenedSaddleStrainRemainder scales (cascadePairedMotion prepared) graph coordinate index
  let growth := 2 * Real.sqrt 2 * scales.omega (index.val + 1)
  have growthPositive : 0 < growth := by
    dsimp only [growth]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by norm_num)))
      (scales.omega_pos frequencyPositive ratioPositive _)
  obtain ⟨inputContinuous, unstableIdentity, _, _, stableWeighted⟩ :=
    factory prepared path index nonterminal finish finishNonnegative finishBound small
  refine ⟨growthPositive, inputContinuous, ?_, ?_, ?_⟩
  · intro time inside
    rw [unstableIdentity time inside, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro current _
    change Real.exp (-growth * time) *
      (Real.exp (growth * (time - current)) * (leading current + remainder current).1) =
        Real.exp (-growth * current) * (leading current + remainder current).1
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · have bound := stableWeighted growth (by linarith : -growth < growth)
    have multiplied := (le_div_iff₀ (show 0 < growth + growth by linarith)).mp bound
    change (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) *
      (growth + growth) ≤
        ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time + remainder time).2| at multiplied
    change growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
      (1 / 2 : ℝ) * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time + remainder time).2|)
    nlinarith
  · intro time
    constructor
    · exact (abs_add _ _).trans (add_le_add_left (by
        simpa only [Real.norm_eq_abs] using norm_fst_le (remainder time)) _)
    · exact (abs_add _ _).trans (add_le_add_left (by
        simpa only [Real.norm_eq_abs] using norm_snd_le (remainder time)) _)

end EulerNonuniqueness.Paper
