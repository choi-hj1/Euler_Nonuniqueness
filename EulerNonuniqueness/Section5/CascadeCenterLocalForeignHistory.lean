import EulerNonuniqueness.Section5.CascadeCenterLocalForeignWeightedReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem intervalIntegrable_of_unit_exponential_weight {function : ℝ → ℝ} {finish : ℝ}
    (weighted : IntervalIntegrable (fun time => Real.exp (-(1 : ℝ) * time) * function time) volume 0 finish) :
    IntervalIntegrable function volume 0 finish := by
  have actual := weighted.continuousOn_mul (Real.continuous_exp.continuousOn : ContinuousOn Real.exp (uIcc 0 finish))
  convert actual using 1
  funext time
  rw [neg_one_mul, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

theorem exists_uniform_actual_center_local_foreign_history :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 →
    ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {scaleRoot boundaryConstant threshold referenceConstant tolerance : ℝ},
    1 ≤ scaleRoot → 1 ≤ boundaryConstant → threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 0 < tolerance →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, index.val + 1 < count → ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, |radialShape prepared.trajectory.movingFamily.patchMotion time index| ≤ 1 / 2) →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let location := changed.location (index.val + 1)
    let length := changed.length (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let patchRadius := factor / 39321600 * length
    let translation := fun time => ‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location
    let external := fun (patch : Fin 4) (time : ℝ) =>
      ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
        biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    let majorant := fun time =>
      tolerance * (‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
        prepared.rawSourceCenteredState time index) +
      (∑ patch : Fin 4, external patch time) / (4 * location) +
      constant * changed.omega (index.val + 1) * (length / location) * epsilon *
        (prepared.rawSourceCenteredState time index + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * (length / location) * epsilon * ∑ patch : Fin 4, foreign patch time
    ContinuousOn translation (Icc 0 finish) ∧ IntervalIntegrable translation volume 0 finish ∧
      (∀ patch : Fin 4, IntervalIntegrable (external patch) volume 0 finish) ∧
      (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
      IntervalIntegrable majorant volume 0 finish ∧
      ∀ time ∈ Icc 0 finish, translation time ≤ ∫ current in (0 : ℝ)..time, majorant current := by
  obtain ⟨pointwiseCap, pointwisePositive, pointwiseFactory⟩ := exists_uniform_actual_prehit_center_local_foreign_return
  obtain ⟨weightedCap, weightedPositive, weightedFactory⟩ := exists_uniform_actual_center_local_foreign_weighted_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min pointwiseCap (min weightedCap continuityCap)
  have capPositive : 0 < rawCap := lt_min pointwisePositive (lt_min weightedPositive continuityPositive)
  have pointwiseCapBound : rawCap ≤ pointwiseCap := min_le_left _ _
  have weightedCapBound : rawCap ≤ weightedCap := (min_le_right _ _).trans (min_le_left _ _)
  have continuityCapBound : rawCap ≤ continuityCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, pointwiseParameters⟩ := pointwiseFactory factorPositive factorSmall
  obtain ⟨_, _, weightedParameters⟩ := weightedFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  filter_upwards [pointwiseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative tolerancePositive,
    weightedParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall
      referenceNonnegative (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency pointwiseEstimate weightedEstimate frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let location := changed.location (index.val + 1)
  let length := changed.length (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let patchRadius := factor / 39321600 * length
  let translation := fun time => ‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location
  let external := fun (patch : Fin 4) (time : ℝ) =>
    ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
      biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖
  let velocity := fun time => ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location
  let majorant := fun time => tolerance * (moment time + center time) + (∑ patch : Fin 4, external patch time) / (4 * location) +
    constant * changed.omega (index.val + 1) * (length / location) * epsilon * (center time + raw time) +
    constant * (length / location) * epsilon * ∑ patch : Fin 4, foreign patch time
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have locationPositive : 0 < location := changed.location_pos _
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have translationContinuous : Continuous translation :=
    ((first.quadrupoleCenter_continuous index).sub (second.quadrupoleCenter_continuous index)).norm.div_const _
  have velocityContinuous : Continuous velocity :=
    ((prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity_continuous 0 index).sub
      (prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity_continuous 1 index)).norm.div_const _
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _ (fun patch _ =>
    ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := by
    have actual : ContinuousOn (fun time => relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time) (Icc 0 finish) :=
      fun time inside => (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
        (subset inside)).continuousAt.continuousWithinAt
    rw [prepared.referenceIdentity] at actual
    exact actual.norm
  obtain ⟨_, weightedExternal, weightedForeign, _⟩ := weightedEstimate count phase dipoleAngle
    (prepared.enlargeCap weightedCapBound) path index nonterminal finish finishNonnegative finishBound radialSmall 1 (by norm_num)
  have externalIntegrable (patch : Fin 4) : IntervalIntegrable (external patch) volume 0 finish := by
    apply intervalIntegrable_of_unit_exponential_weight
    exact weightedExternal patch
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable (foreign patch) volume 0 finish := by
    apply intervalIntegrable_of_unit_exponential_weight
    exact weightedForeign patch
  have externalSumIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, external patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun patch _ => externalIntegrable patch)
  have foreignSumIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, foreign patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun patch _ => foreignIntegrable patch)
  have centerIntegrable := centerContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawIntegrable := rawContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have momentIntegrable := momentContinuous.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have majorantIntegrable : IntervalIntegrable majorant volume 0 finish := by
    exact (((((momentIntegrable.add centerIntegrable).const_mul tolerance).add (externalSumIntegrable.div_const (4 * location))).add
      ((centerIntegrable.add rawIntegrable).const_mul (constant * changed.omega (index.val + 1) * (length / location) * epsilon))).add
      (foreignSumIntegrable.const_mul (constant * (length / location) * epsilon)))
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : velocity time ≤ majorant time := by
    have actual := pointwiseEstimate count phase dipoleAngle (prepared.enlargeCap pointwiseCapBound) path index nonterminal
      finish finishNonnegative finishBound radialSmall time inside
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, majorant, moment, center, raw, foreign, external, velocity,
        first, second, changed, epsilon, patchRadius, location, length,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  refine ⟨translationContinuous.continuousOn, translationContinuous.intervalIntegrable 0 finish,
    externalIntegrable, foreignIntegrable, majorantIntegrable, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have original := path.relative_center_original_history index nonterminal (subset inside)
  rw [prepared.referenceIdentity] at original
  have normBound := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := (0 : ℝ)) (b := time)
    (f := fun current => prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index current -
      prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index current) inside.1
  rw [← original] at normBound
  have divided := div_le_div_of_nonneg_right normBound locationPositive.le
  rw [← intervalIntegral.integral_div] at divided
  have upperIntegrable : IntervalIntegrable majorant volume 0 time := majorantIntegrable.mono_set (by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact prefixSubset)
  have comparison := intervalIntegral.integral_mono_on (μ := volume) inside.1
    (velocityContinuous.intervalIntegrable 0 time) upperIntegrable (fun current member => pointwise current (prefixSubset member))
  exact divided.trans comparison

end EulerNonuniqueness.Paper
