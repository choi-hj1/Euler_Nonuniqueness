import EulerNonuniqueness.Section5.CascadePrehitFirstMomentMacroFeedback
import EulerNonuniqueness.Section5.CascadeFirstMomentSaddleWeight
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section5.CascadePrehitExternalDilationReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6 FiniteMovingPatchFamily

private theorem divide_firstMoment_source_defect
    {distancePower defect constant strain center row macroState : ℝ}
    (positive : 0 < distancePower)
    (bound : distancePower * defect ≤ constant * strain * distancePower * center + constant * row * macroState) :
    defect ≤ constant * strain * center + (constant / distancePower) * row * macroState := by
  apply (mul_le_mul_left positive).mp
  calc
    distancePower * defect ≤ constant * strain * distancePower * center + constant * row * macroState := bound
    _ = distancePower * (constant * strain * center + (constant / distancePower) * row * macroState) := by
      field_simp [ne_of_gt positive]; ring

theorem exists_uniform_actual_firstMoment_weighted_macro_feedback :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    let changed : Scales := {scales with frequency := frequency}
    let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time‖) ≤
      constant * changed.strain *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      (constant / changed.location (index.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖) := by
  obtain ⟨defectCap, defectPositive, feedback⟩ := exists_uniform_actual_prehit_firstMoment_macro_feedback
  obtain ⟨continuityCap, continuityPositive, rawContinuity⟩ := exists_uniform_actual_raw_spectral_continuity
  let rawCap := min defectCap continuityCap
  have rawPositive : 0 < rawCap := lt_min defectPositive continuityPositive
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, parameters⟩ := feedback factorPositive factorSmall
  refine ⟨2 * constant, mul_nonneg (by norm_num) constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [parameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne,
    scales.eventually_cascade_firstMoment_weighted_source_defect amplitudePositive ratioBound alphaPositive,
    scales.eventually_uniform_firstMoment_saddle_weight ratioBound alphaPositive,
    eventually_gt_atTop (0 : ℝ)] with frequency pointwiseHistory weightedHistory weights frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let weight := 2 * Real.sqrt 2 * changed.omega (index.val + 1)
  let center := fun time => prepared.rawSourceCenteredState time index
  let macroEnvelope := fun time => ‖fun source : Fin count =>
    changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let defect := relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let curve := relativeNormalizedFirstMoment changed prepared.trajectory.movingFamily.patchMotion prepared.reference index
  let row := 216360000 * changed.hessian + 576 * changed.strain
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightPositive : 0 < weight := (weights (index.val + 1)).1
  have rawContinuous (source : Fin count) (patch : Fin 4) :
      ContinuousOn (fun time => prepared.rawSourceShapeBudget time source patch) (Icc 0 finish) := by
    obtain ⟨first, final⟩ := rawContinuity prepared rawPositive (min_le_right _ _) path (finProdFinEquiv (source, patch))
    have firstProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn (first.mono subset)
    have finalProjection : ContinuousOn (fun time => diskPhysicalTransverseProjection
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskPhysicalTransverseProjection.continuous.comp_continuousOn (final.mono subset)
    have firstNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn (first.mono subset)
    have finalNeutral : ContinuousOn (fun time => diskNeutralCLM
        (prepared.trajectory.spectralCoordinate (finProdFinEquiv (source, patch)) time)) (Icc 0 finish) :=
      diskNeutralCLM.continuous.comp_continuousOn (final.mono subset)
    unfold CascadeSourcePreparedPair.rawSourceShapeBudget
    with_reducible_and_instances
      exact (firstProjection.sub finalProjection).norm.add
        ((firstProjection.norm.add finalProjection.norm).mul (firstNeutral.sub finalNeutral).norm)
  let first := prepared.referenceWitness.trajectory.movingFamily
  let final := prepared.trajectory.movingFamily
  have centroidContinuous (family : FiniteMovingPatchFamily (count * 4))
      (interior : ∀ label, Icc (0 : ℝ) finish ⊆ Ioo (family.patch label).initialTime (family.patch label).finalTime)
      (source : Fin count) (patch : Fin 4) :
      ContinuousOn (fun time => patchCentroid family.patchMotion time source patch) (Icc 0 finish) := by
    simp_rw [FiniteMovingPatchFamily.patchCentroid_eq]
    exact fun time inside => ((family.patch _).centroid_contDiffAt (interior _ inside)).continuousAt.continuousWithinAt
  have firstInterior (label : Fin (count * 4)) : Icc (0 : ℝ) finish ⊆ Ioo (first.patch label).initialTime (first.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
  have finalInterior (label : Fin (count * 4)) : Icc (0 : ℝ) finish ⊆ Ioo (final.patch label).initialTime (final.patch label).finalTime := by
    intro time inside
    change time ∈ Ioo (-(1 : ℝ)) 3
    exact ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
  have firstCenter (source : Fin count) : ContinuousOn (fun time => quadrupoleCenter first.patchMotion time source) (Icc 0 finish) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous first firstInterior source patch)).div_const 4
  have finalCenter (source : Fin count) : ContinuousOn (fun time => quadrupoleCenter final.patchMotion time source) (Icc 0 finish) :=
    (continuousOn_finset_sum _ (fun patch _ => centroidContinuous final finalInterior source patch)).div_const 4
  have centeredContinuous : ContinuousOn (fun time =>
      (fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index) -
      (fun patch => patchCentroid final.patchMotion time index patch - quadrupoleCenter final.patchMotion time index)) (Icc 0 finish) :=
    continuousOn_pi.mpr fun patch =>
      ((centroidContinuous first firstInterior index patch).sub (firstCenter index)).sub
        ((centroidContinuous final finalInterior index patch).sub (finalCenter index))
  have centerContinuous : ContinuousOn center (Icc 0 finish) := centeredContinuous.norm.div_const _
  have macroStateContinuous (source : Fin count) : ContinuousOn (fun time => prepared.macroSourceState time source) (Icc 0 finish) := by
    have gaugeContinuous (family : FiniteMovingPatchFamily (count * 4)) (patch : Fin 4) :
        ContinuousOn (fun time => family.cascadeCenters time (source, patch)) (Icc 0 finish) :=
      fun time _ => ((family.patch _).center_equation time).continuousAt.continuousWithinAt
    have centeredSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
      (((gaugeContinuous first patch).sub (firstCenter source)).sub
        ((gaugeContinuous final patch).sub (finalCenter source))).norm)
    have rawSum := continuousOn_finset_sum Finset.univ (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => rawContinuous source patch)
    have identity : (fun time => prepared.macroSourceState time source) = fun time =>
        (‖quadrupoleCenter first.patchMotion time source - quadrupoleCenter final.patchMotion time source‖ +
          ∑ patch : Fin 4, ‖(first.cascadeCenters time (source, patch) - quadrupoleCenter first.patchMotion time source) -
            (final.cascadeCenters time (source, patch) - quadrupoleCenter final.patchMotion time source)‖) /
          changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch := by
      funext time
      with_reducible_and_instances
        dsimp only [CascadeSourcePreparedPair.macroSourceState, CascadeSourcePreparedPair.rawSourceShapeBudget,
          MovingCentroidGaugeTrajectory.spectralCoordinate, first, final, changed]
    rw [identity]
    exact ((((firstCenter source).sub (finalCenter source)).norm.add centeredSum).div_const
      (changed.location (source.val + 1))).add rawSum
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr fun source => continuousOn_const.mul (macroStateContinuous source)).norm
  have curveContinuous : ContinuousOn curve (Icc 0 finish) := fun time inside =>
    (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
      (subset inside)).continuousAt.continuousWithinAt
  have velocityContinuous := (path.relativeFirstMomentExternalVelocity_continuousOn
    amplitudePositive frequencyPositive ratioPositive index).mono subset
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuous_max.comp_continuousOn
      (continuousOn_const.prodMk (velocityContinuous.norm.sub (continuousOn_const.mul curveContinuous.norm)))
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have macroIntegrable := (weightContinuous.continuousOn.mul macroContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have defectIntegrable := (weightContinuous.continuousOn.mul defectContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have momentIntegrable := (weightContinuous.continuousOn.mul curveContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let enlarged := prepared.enlargeCap (min_le_left defectCap continuityCap)
  have macroArrayIdentity (time : ℝ) :
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * enlarged.macroSourceState time source) =
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
    funext source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, enlarged, CascadeSourcePreparedPair.enlargeCap]
  have centerIdentity (time : ℝ) :
      ‖quadrupoleNormalizedCentroidOffsets prepared.trajectory.movingFamily.patchMotion index time (changed.length (index.val + 1)) -
        quadrupoleNormalizedCentroidOffsets prepared.reference index time (changed.length (index.val + 1))‖ = center time := by
    rw [quadrupoleNormalizedCentroidOffsets_relative_norm_eq_div _ _ _ _ (changed.length_pos _), norm_sub_rev,
      prepared.referenceIdentity]
    rfl
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      defect time ≤ constant * changed.strain * center time +
        (constant / changed.location (index.val + 1) ^ 4) * row * macroEnvelope time := by
    have actual := pointwiseHistory count phase dipoleAngle enlarged path index nonterminal finish finishNonnegative
      finishBound radialSmall time inside
    dsimp only at actual
    rw [macroArrayIdentity] at actual
    dsimp only [enlarged, CascadeSourcePreparedPair.enlargeCap] at actual
    with_reducible_and_instances
      change changed.location (index.val + 1) ^ 4 * defect time ≤
        constant * changed.strain * changed.location (index.val + 1) ^ 4 *
          ‖quadrupoleNormalizedCentroidOffsets prepared.trajectory.movingFamily.patchMotion index time
              (changed.length (index.val + 1)) -
            quadrupoleNormalizedCentroidOffsets prepared.reference index time (changed.length (index.val + 1))‖ +
        constant * row * macroEnvelope time at actual
    rw [centerIdentity] at actual
    exact divide_firstMoment_source_defect (pow_pos (changed.location_pos _) 4) actual
  have upperContinuous : ContinuousOn (fun time => constant * changed.strain * center time +
      (constant / changed.location (index.val + 1) ^ 4) * row * macroEnvelope time) (Icc 0 finish) :=
    (continuousOn_const.mul centerContinuous).add (continuousOn_const.mul macroContinuous)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative defectIntegrable
    ((weightContinuous.continuousOn.mul upperContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative)
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have integralIdentity :
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        (constant * changed.strain * center time + (constant / changed.location (index.val + 1) ^ 4) * row * macroEnvelope time)) =
      constant * changed.strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      (constant / changed.location (index.val + 1) ^ 4) * row *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * macroEnvelope time) := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) (constant * changed.strain),
      mul_left_comm (Real.exp _) ((constant / changed.location (index.val + 1) ^ 4) * row)]
    rw [intervalIntegral.integral_add (centerIntegrable.const_mul _) (macroIntegrable.const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  have normalizedComparison := comparison.trans_eq integralIdentity
  have history := weightedHistory prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound
  have multiplied := mul_le_mul_of_nonneg_left history weightPositive.le
  have coefficientIdentity : weight * (2 / weight) = 2 := by field_simp
  rw [← mul_assoc, coefficientIdentity] at multiplied
  have actual := multiplied.trans (mul_le_mul_of_nonneg_left normalizedComparison (by norm_num : (0 : ℝ) ≤ 2))
  convert actual using 1; ring

end EulerNonuniqueness.Paper
