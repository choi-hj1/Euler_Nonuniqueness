import EulerNonuniqueness.Section5.CascadeMacroStateCenteredBound
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_macro_state_weighted_return :
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
    ∀ source : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    ∀ weight : ℝ, ({scales with frequency := frequency}).omega (source.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.macroSourceState time source) ≤
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (‖quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source -
          quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ / changed.location (source.val + 1))) +
      (4 * weight * changed.length (source.val + 1) / changed.location (source.val + 1) +
        constant * changed.omega (source.val + 1)) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time source) +
      (constant / changed.location (source.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖fun other : Fin count => changed.location (other.val + 1) ^ 4 * prepared.macroSourceState time other‖) := by
  obtain ⟨feedbackCap, feedbackPositive, feedback⟩ := exists_uniform_actual_raw_source_weighted_feedback
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
  intro count phase dipoleAngle shapeRadius monitor prepared path source finish finishNonnegative finishBound weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let translation := fun time =>
    ‖quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ / changed.location (source.val + 1)
  let center := fun time => prepared.rawSourceCenteredState time source
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let macroEnvelope := fun time => ‖fun other : Fin count =>
    changed.location (other.val + 1) ^ 4 * prepared.macroSourceState time other‖
  let centerCoefficient := 4 * (changed.length (source.val + 1) / changed.location (source.val + 1))
  let foreignCoefficient := (constant / changed.location (source.val + 1) ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  let weighted := fun value : ℝ → ℝ => ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * value time
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightPositive : 0 < weight := (changed.omega_pos frequencyPositive ratioPositive _).trans_le weightBound
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have actualContinuity (other : Fin count) := continuity prepared rawPositive (min_le_right _ _) path other
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => ((actualContinuity source).1 patch).mono subset)
  have centerContinuous : ContinuousOn center (Icc 0 finish) := (actualContinuity source).2.1.mono subset
  have translationContinuous : ContinuousOn translation (Icc 0 finish) := (actualContinuity source).2.2.1.mono subset
  have macroContinuous : ContinuousOn (fun time => prepared.macroSourceState time source) (Icc 0 finish) :=
    (actualContinuity source).2.2.2.mono subset
  have envelopeContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr fun other => continuousOn_const.mul ((actualContinuity other).2.2.2.mono subset)).norm
  have upperContinuous : ContinuousOn (fun time => translation time + centerCoefficient * center time + raw time)
      (Icc 0 finish) := (translationContinuous.add (continuousOn_const.mul centerContinuous)).add rawContinuous
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have translationIntegrable := (exponentialContinuous.continuousOn.mul translationContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have centerIntegrable := (exponentialContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have rawIntegrable := (exponentialContinuous.continuousOn.mul rawContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have macroIntegrable := (exponentialContinuous.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have envelopeIntegrable := (exponentialContinuous.continuousOn.mul envelopeContinuous).intervalIntegrable_of_Icc
    (μ := volume) finishNonnegative
  have geometric := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative macroIntegrable
    ((exponentialContinuous.continuousOn.mul upperContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (prepared.macroSourceState_le_centered_and_raw path (subset inside) source)
      (Real.exp_pos _).le)
  have integralIdentity :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (translation time + centerCoefficient * center time + raw time)) =
      weighted translation + centerCoefficient * weighted center + weighted raw := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) centerCoefficient]
    rw [intervalIntegral.integral_add (translationIntegrable.add (centerIntegrable.const_mul _)) rawIntegrable,
      intervalIntegral.integral_add translationIntegrable (centerIntegrable.const_mul _),
      intervalIntegral.integral_const_mul]
  have weightedGeometry := mul_le_mul_of_nonneg_left (geometric.trans_eq integralIdentity) weightPositive.le
  let enlarged := prepared.enlargeCap (min_le_left feedbackCap continuityCap)
  have rawBound := rawFeedback count phase dipoleAngle enlarged path source finish finishNonnegative finishBound weight weightBound
  have normalizedFeedback : weight * weighted raw ≤
      constant * changed.omega (source.val + 1) * weighted center + foreignCoefficient * weighted macroEnvelope := by
    with_reducible_and_instances
      dsimp only [weighted, raw, center, macroEnvelope, foreignCoefficient, changed,
        CascadeSourcePreparedPair.rawSourceShapeBudget, CascadeSourcePreparedPair.rawSourceCenteredState,
        CascadeSourcePreparedPair.macroSourceState, MovingCentroidGaugeTrajectory.spectralCoordinate,
        enlarged, CascadeSourcePreparedPair.enlargeCap] at rawBound ⊢
      exact rawBound
  change weight * weighted (fun time => prepared.macroSourceState time source) ≤
    weight * weighted translation +
      (4 * weight * changed.length (source.val + 1) / changed.location (source.val + 1) +
        constant * changed.omega (source.val + 1)) * weighted center + foreignCoefficient * weighted macroEnvelope
  calc
    _ ≤ weight * (weighted translation + centerCoefficient * weighted center + weighted raw) := weightedGeometry
    _ = weight * weighted translation + weight * centerCoefficient * weighted center + weight * weighted raw := by ring
    _ ≤ weight * weighted translation + weight * centerCoefficient * weighted center +
        (constant * changed.omega (source.val + 1) * weighted center + foreignCoefficient * weighted macroEnvelope) :=
      add_le_add_left normalizedFeedback _
    _ = _ := by dsimp only [centerCoefficient]; ring

end EulerNonuniqueness.Paper
