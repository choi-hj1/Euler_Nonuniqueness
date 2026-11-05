import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedLocalForeignReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 750000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_macro_state_weighted_local_foreign_return :
    ∃ rawCap > (0 : ℝ), ∀ factor : ℝ, 0 < factor → factor ≤ 1 →
    ∃ constant ≥ (0 : ℝ), ∃ rootMin ≥ (8 : ℝ),
    ∀ (scales : Scales) (scaleRoot : ℝ), rootMin ≤ scaleRoot → scales.amplitude = scaleRoot ^ 3 →
    2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ threshold referenceConstant boundaryConstant : ℝ, threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ boundaryConstant →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    ∀ weight : ℝ, ({scales with frequency := frequency}).omega (index.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.referenceWitness.trajectory.movingFamily
    let final := prepared.trajectory.movingFamily
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch)
          (changed.radius (index.val + 1)) (power + 1) time -
        final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid final.patchMotion current index patch)
          (changed.radius (index.val + 1)) (power + 1) time‖
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.macroSourceState time index) volume 0 finish ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time index) ≤
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter final.patchMotion time index‖ /
          changed.location (index.val + 1))) +
      (4 * weight * changed.length (index.val + 1) / changed.location (index.val + 1) +
        constant * changed.omega (index.val + 1)) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      constant * ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
  obtain ⟨feedbackCap, feedbackPositive, feedback⟩ := exists_uniform_actual_raw_source_weighted_local_foreign_return
  obtain ⟨continuityCap, continuityPositive, continuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min feedbackCap continuityCap
  have rawPositive : 0 < rawCap := lt_min feedbackPositive continuityPositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, rootMin, rootEight, parameters⟩ := feedback factor factorPositive factorSmall
  refine ⟨constant, constantNonnegative, rootMin, rootEight, ?_⟩
  intro scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant boundaryConstant
    thresholdSmall referenceNonnegative boundaryOne orbit sectionTime
  filter_upwards [parameters scales scaleRoot rootLarge amplitudeIdentity ratioBound alphaPositive threshold referenceConstant
      boundaryConstant thresholdSmall referenceNonnegative boundaryOne orbit sectionTime,
    eventually_gt_atTop (0 : ℝ)] with frequency rawFeedback frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time -
      final.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid final.patchMotion current index patch)
        (changed.radius (index.val + 1)) (power + 1) time‖
  let translation := fun time => ‖quadrupoleCenter first.patchMotion time index -
    quadrupoleCenter final.patchMotion time index‖ / changed.location (index.val + 1)
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let centerCoefficient := 4 * (changed.length (index.val + 1) / changed.location (index.val + 1))
  let weighted := fun function : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * function time
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightPositive : 0 < weight := (changed.omega_pos frequencyPositive ratioPositive _).trans_le weightBound
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have actualContinuity := continuity prepared rawPositive (min_le_right _ _) path index
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => (actualContinuity.1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) := actualContinuity.2.1.mono subset
  have translationContinuous : ContinuousOn translation (Icc 0 finish) := actualContinuity.2.2.1.mono subset
  have macroContinuous : ContinuousOn (fun time => prepared.macroSourceState time index) (Icc 0 finish) :=
    actualContinuity.2.2.2.mono subset
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have rawIntegrable := (exponentialContinuous.continuousOn.mul rawContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have centerIntegrable := (exponentialContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have translationIntegrable := (exponentialContinuous.continuousOn.mul translationContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have macroIntegrable := (exponentialContinuous.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let enlarged := prepared.enlargeCap (min_le_left feedbackCap continuityCap)
  obtain ⟨foreignIntegrable, _, rawBound⟩ := rawFeedback count phase dipoleAngle enlarged path index finish
    finishNonnegative finishBound weight weightBound
  have actualForeignIntegrable (patch : Fin 4) : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish := by
    have actual := foreignIntegrable patch
    with_reducible_and_instances
      dsimp only [foreign, changed, first, final, enlarged, CascadeSourcePreparedPair.enlargeCap] at actual ⊢
      exact actual
  have actualRawBound : weight * weighted raw ≤ constant * changed.omega (index.val + 1) * weighted center +
      constant * ∑ patch : Fin 4, weighted (foreign patch) := by
    with_reducible_and_instances
      dsimp only [weighted, raw, center, foreign, changed, first, final, enlarged, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceShapeBudget, CascadeSourcePreparedPair.rawSourceCenteredState,
        MovingCentroidGaugeTrajectory.spectralCoordinate] at rawBound ⊢
      exact rawBound
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (translation time + centerCoefficient * center time + raw time)) volume 0 finish := by
    convert (translationIntegrable.add (centerIntegrable.const_mul centerCoefficient)).add rawIntegrable using 1
    funext time
    ring
  have geometric := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative macroIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (prepared.macroSourceState_le_centered_and_raw path (subset inside) index)
      (Real.exp_pos _).le)
  have integralIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (translation time + centerCoefficient * center time + raw time)) =
      weighted translation + centerCoefficient * weighted center + weighted raw := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) centerCoefficient]
    rw [intervalIntegral.integral_add (translationIntegrable.add (centerIntegrable.const_mul _)) rawIntegrable,
      intervalIntegral.integral_add translationIntegrable (centerIntegrable.const_mul _), intervalIntegral.integral_const_mul]
  rw [integralIdentity] at geometric
  have actual := (mul_le_mul_of_nonneg_left geometric weightPositive.le).trans
    (show weight * (weighted translation + centerCoefficient * weighted center + weighted raw) ≤
      weight * weighted translation + (weight * centerCoefficient + constant * changed.omega (index.val + 1)) * weighted center +
        constant * ∑ patch : Fin 4, weighted (foreign patch) by nlinarith only [actualRawBound])
  refine ⟨actualForeignIntegrable, macroIntegrable, ?_⟩
  convert actual using 1 <;> dsimp only [centerCoefficient, weighted, translation, center, foreign, changed, first, final] <;> ring

end EulerNonuniqueness.Paper
