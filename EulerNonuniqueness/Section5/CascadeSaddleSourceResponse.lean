import EulerNonuniqueness.Section5.CascadeSaddleWeightedResponse
import EulerNonuniqueness.Section5.CascadeLeadingStrainContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem exists_uniform_cascade_saddle_source_response
    {graph coordinate : ℝ → ℝ} (graphSmooth : ContDiffAt ℝ 2 graph 0)
    (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0) :
    ∃ radius > (0 : ℝ), radius ≤ 1 / 4 ∧
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, index.val + 1 < count →
    ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish,
      |unstableShape prepared.trajectory.movingFamily.patchMotion time index| +
        |stableShape prepared.trajectory.movingFamily.patchMotion time index| ≤ radius) →
    let changed : Scales := {scales with frequency := frequency}
    let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
      referenceStraightenedShape prepared.reference graph coordinate index time
    let leading := fun time => quadrupoleRelativeLeadingStrain changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference time index
    let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate index
    let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    0 < growth ∧ ContinuousOn leading (Icc 0 finish) ∧ ContinuousOn remainder (Icc 0 finish) ∧
    (∀ time ∈ Icc 0 finish,
      Real.exp (-growth * time) * (relative time).1 =
        (∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (leading current).1) +
          ∫ current in (0 : ℝ)..time, Real.exp (-growth * current) * (remainder current).1) ∧
    (∀ time ∈ Icc 0 finish,
      |(relative time).2| ≤ ∫ current in (0 : ℝ)..time,
        Real.exp (-growth * (time - current)) * (|(leading current).2| + ‖remainder current‖)) ∧
    growth * (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(relative time).2|) ≤
      (1 / 2 : ℝ) * ((∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time).2|) +
        ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖remainder time‖) := by
  obtain ⟨weightedRadius, weightedPositive, weightedQuarter, weighted⟩ :=
    exists_uniform_cascade_saddle_weighted_response graphSmooth coordinateSmooth
  obtain ⟨pointRadius, pointPositive, _, point⟩ :=
    exists_uniform_cascade_saddle_original_duhamel graphSmooth coordinateSmooth
  let baseRadius := min weightedRadius pointRadius
  let radius := baseRadius / 2
  have basePositive : 0 < baseRadius := lt_min weightedPositive pointPositive
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have radiusBase : radius < baseRadius := by dsimp only [radius]; linarith
  refine ⟨radius, radiusPositive, radiusBase.le.trans ((min_le_left _ _).trans weightedQuarter), ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [eventually_gt_atTop (0 : ℝ),
    scales.eventually_cascade_relative_leading_strain_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_reference_sharp_defect_small ratioBound alphaPositive referenceNonnegative basePositive]
    with frequency frequencyPositive leadingContinuous referenceSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound small
  let changed : Scales := {scales with frequency := frequency}
  let relative := fun time => referenceStraightenedShape prepared.trajectory.movingFamily.patchMotion graph coordinate index time -
    referenceStraightenedShape prepared.reference graph coordinate index time
  let leading := fun time => quadrupoleRelativeLeadingStrain changed prepared.trajectory.movingFamily.patchMotion
    prepared.reference time index
  let remainder := relativeStraightenedSaddleStrainRemainder changed (cascadePairedMotion prepared) graph coordinate index
  let growth := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  have pairedSmall (side : Fin 2) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |unstableShape (cascadePairedMotion prepared side) time index| +
        |stableShape (cascadePairedMotion prepared side) time index| < baseRadius := by
    fin_cases side
    · exact (small time inside).trans_lt radiusBase
    · have actual := referenceSmall prepared time ⟨inside.1, inside.2.trans (finishBound.trans path.stopBound)⟩ index
      change |unstableShape prepared.reference time index| + |stableShape prepared.reference time index| < baseRadius
      linarith [abs_nonneg (diagonalDifference prepared.reference time index / changed.length (index.val + 1) ^ 2 - 1)]
  obtain ⟨growthPositive, inputContinuous, unstableCoefficient, stableWeighted, sourceBound⟩ :=
    weighted frequencyPositive (by change 0 < scales.ratio; linarith) prepared path index nonterminal
      finish finishNonnegative finishBound
      (fun side time inside => (pairedSmall side time inside).trans_le (min_le_left _ _))
  obtain ⟨_, _, _, stablePoint, _⟩ := point prepared path index nonterminal finish finishNonnegative finishBound
    (fun side time inside => (pairedSmall side time inside).trans_le (min_le_right _ _))
  have leadingOn : ContinuousOn leading (Icc 0 finish) :=
    (leadingContinuous count phase dipoleAngle prepared path index).mono (Icc_subset_Icc le_rfl finishBound)
  have remainderOn : ContinuousOn remainder (Icc 0 finish) := by
    have actual := inputContinuous.sub leadingOn
    apply actual.congr
    intro time inside
    change remainder time = leading time + remainder time - leading time
    abel
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-growth * time)) := by fun_prop
  have leadingIntegrable := (weightContinuous.continuousOn.mul leadingOn.fst).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have remainderIntegrable := (weightContinuous.continuousOn.mul remainderOn.fst).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  refine ⟨growthPositive, leadingOn, remainderOn, ?_, ?_, ?_⟩
  · intro time inside
    rw [unstableCoefficient time inside]
    simp_rw [Prod.fst_add, mul_add]
    exact intervalIntegral.integral_add
      (leadingIntegrable.mono_set (by rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact Icc_subset_Icc le_rfl inside.2))
      (remainderIntegrable.mono_set (by rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]; exact Icc_subset_Icc le_rfl inside.2))
  · intro time inside
    have subset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    have kernelContinuous : Continuous (fun current : ℝ => Real.exp (-growth * (time - current))) := by fun_prop
    have actual := stablePoint time inside
    apply actual.trans
    exact intervalIntegral.integral_mono_on (μ := volume) inside.1
      ((kernelContinuous.continuousOn.mul ((inputContinuous.mono subset).snd.abs)).intervalIntegrable_of_Icc inside.1)
      ((kernelContinuous.continuousOn.mul (((leadingOn.mono subset).snd.abs).add
        (remainderOn.mono subset).norm)).intervalIntegrable_of_Icc inside.1)
      (fun current _ => mul_le_mul_of_nonneg_left (sourceBound current).2 (Real.exp_pos _).le)
  · have sourceIntegral := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative
      ((weightContinuous.continuousOn.mul inputContinuous.snd.abs).intervalIntegrable_of_Icc finishNonnegative)
      ((weightContinuous.continuousOn.mul (leadingOn.snd.abs.add remainderOn.norm)).intervalIntegrable_of_Icc finishNonnegative)
      (fun time _ => mul_le_mul_of_nonneg_left (sourceBound time).2 (Real.exp_pos _).le)
    have split : (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * (|(leading time).2| + ‖remainder time‖)) =
        (∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * |(leading time).2|) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-growth * time) * ‖remainder time‖ := by
      simp_rw [mul_add]
      exact intervalIntegral.integral_add
        ((weightContinuous.continuousOn.mul leadingOn.snd.abs).intervalIntegrable_of_Icc finishNonnegative)
        ((weightContinuous.continuousOn.mul remainderOn.norm).intervalIntegrable_of_Icc finishNonnegative)
    rw [split] at sourceIntegral
    exact stableWeighted.trans (mul_le_mul_of_nonneg_left sourceIntegral (by norm_num))

end EulerNonuniqueness.Paper
