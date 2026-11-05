import EulerNonuniqueness.Section5.CascadeDilationLocalForeignWeightedReturn

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem intervalIntegrable_of_exponential_weight {function : ℝ → ℝ} {weight start finish : ℝ}
    (integrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * function time) volume start finish) :
    IntervalIntegrable function volume start finish := by
  have continuous : Continuous (fun time : ℝ => Real.exp (weight * time)) := by fun_prop
  have actual := integrable.continuousOn_mul continuous.continuousOn
  convert actual using 1
  ext time
  rw [← mul_assoc, ← Real.exp_add]
  simp only [← add_mul, add_neg_cancel, zero_mul, Real.exp_zero, one_mul]

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_prehit_dilation_local_foreign_history :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 100 → ∃ constant ≥ (0 : ℝ),
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
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let centerRadius := factor / 39321600 * changed.location (index.val + 1)
    let patchRadius := factor / 39321600 * changed.length (index.val + 1)
    let dilation := fun time => (diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
      changed.length (index.val + 1) ^ 2
    let velocity := relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    let majorant := fun time =>
      tolerance * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
        (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon) *
          prepared.rawSourceCenteredState time index +
        constant * changed.omega (index.val + 1) * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        constant * difference time + constant * epsilon * ∑ patch : Fin 4, foreign patch time
    ContinuousOn dilation (Icc 0 finish) ∧ ContinuousOn velocity (Icc 0 finish) ∧
    IntervalIntegrable (fun time => |velocity time|) volume 0 finish ∧
    IntervalIntegrable difference volume 0 finish ∧
    (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
    IntervalIntegrable majorant volume 0 finish ∧
    ∀ time ∈ Icc 0 finish, |dilation time| ≤ ∫ current in (0 : ℝ)..time, majorant current := by
  obtain ⟨returnCap, returnPositive, returnFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_return
  obtain ⟨momentCap, momentPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_weighted_return
  obtain ⟨patchCap, patchPositive, patchFactory⟩ := exists_uniform_actual_foreign_patch_coefficient_integrability
  let rawCap := min returnCap (min momentCap patchCap)
  have capPositive : 0 < rawCap := lt_min returnPositive (lt_min momentPositive patchPositive)
  have returnCapBound : rawCap ≤ returnCap := min_le_left _ _
  have momentCapBound : rawCap ≤ momentCap := (min_le_right _ _).trans (min_le_left _ _)
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, returns⟩ := returnFactory factorPositive factorSmall
  obtain ⟨momentConstant, momentNonnegative, moments⟩ := momentFactory factorPositive (factorSmall.trans (by norm_num))
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  filter_upwards [returns scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative tolerancePositive,
    moments scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne
      factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_cascade_dilation_closed_physical_history amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency returnEstimate momentEstimate patchEstimate physicalHistory lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let dilation := fun time => (diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
    changed.length (index.val + 1) ^ 2
  let velocity := relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index
  let mechanical := fun time => (prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 1 index time) / changed.length (index.val + 1) ^ 2
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time
        (factor / 39321600 * changed.location (index.val + 1)) power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time
        (factor / 39321600 * changed.location (index.val + 1)) power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch)
        (factor / 39321600 * changed.length (index.val + 1)) (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch)
        (factor / 39321600 * changed.length (index.val + 1)) (power + 1) time‖
  let majorant := fun time =>
    tolerance * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
      (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon) *
        prepared.rawSourceCenteredState time index +
      constant * changed.omega (index.val + 1) * epsilon * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * difference time + constant * epsilon * ∑ patch : Fin 4, foreign patch time
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt dilation (velocity time) time := by
    simpa only [dilation, velocity, first, second, prepared.referenceIdentity] using
      (physicalHistory prepared.toCascadeMaterialPreparedPair path index nonterminal time (subset inside)).1
  have mechanicalDerivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt dilation (mechanical time) time := by
    have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
      ⟨by linarith [inside.1], by linarith [inside.2, finishBound, path.stopBound]⟩
    simpa only [dilation, mechanical, first, second, cascadePairedMotion, Fin.cases_succ, prepared.referenceIdentity] using
      ((prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 0 index globalInside).sub
        (prepared.toCascadeMaterialPreparedPair.paired_diagonal_hasDerivAt 1 index globalInside)).div_const
          (changed.length (index.val + 1) ^ 2)
  have dilationContinuous : ContinuousOn dilation (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have mechanicalContinuous : Continuous mechanical :=
    ((prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity_continuous 0 index).sub
      (prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity_continuous 1 index)).div_const _
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) :=
    mechanicalContinuous.continuousOn.congr (fun time inside => (derivative time inside).unique (mechanicalDerivative time inside))
  have velocityIntegrable := velocityContinuous.abs.intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let momentPrepared := prepared.enlargeCap momentCapBound
  obtain ⟨weightedDifference, _, weightedCenter, weightedRaw, weightedMoment, _⟩ :=
    momentEstimate count phase dipoleAngle momentPrepared path index nonterminal finish finishNonnegative finishBound radialSmall
  have differenceIntegrable : IntervalIntegrable difference volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedDifference
    simpa only [difference, first, second, momentPrepared, CascadeSourcePreparedPair.enlargeCap] using actual
  have momentIntegrable : IntervalIntegrable
      (fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedMoment
    change IntervalIntegrable (fun time =>
      ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) volume 0 finish at actual
    rw [prepared.referenceIdentity] at actual
    exact actual
  have centerIntegrable : IntervalIntegrable (fun time => prepared.rawSourceCenteredState time index) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedCenter
    with_reducible_and_instances
      dsimp only [momentPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState] at actual ⊢
      exact actual
  have rawIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedRaw
    with_reducible_and_instances
      dsimp only [momentPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  let patchPrepared := prepared.enlargeCap patchCapBound
  let patchRadius := factor / 39321600 * changed.length (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have patchRadiusNonnegative : 0 ≤ patchRadius := by dsimp only [patchRadius]; positivity
  have patchRadiusSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have lengthBound := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ 1 * changed.location (index.val + 1) at lengthBound
    dsimp only [patchRadius]
    have product := mul_le_mul_of_nonneg_left lengthBound (show 0 ≤ factor / 39321600 by positivity)
    have locationPositive := changed.location_pos (index.val + 1)
    change _ ≤ changed.location (index.val + 1) / (100000 * 96)
    nlinarith only [product, locationPositive, mul_nonneg (sub_nonneg.mpr factorSmall) locationPositive.le]
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable (foreign patch) volume 0 finish := by
    have actual := (patchEstimate count phase dipoleAngle patchPrepared path (index, patch) patchRadius patchRadiusNonnegative
      patchRadiusSmall finish finishNonnegative finishBound 0).2.2
    simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul, foreign, patchRadius, first, second,
      patchPrepared, CascadeSourcePreparedPair.enlargeCap] using actual
  have foreignSumIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, foreign patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (f := foreign) (fun patch _ => foreignIntegrable patch)
  have majorantIntegrable : IntervalIntegrable majorant volume 0 finish :=
    ((((momentIntegrable.const_mul tolerance).add
      (centerIntegrable.const_mul (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon))).add
      (rawIntegrable.const_mul (constant * changed.omega (index.val + 1) * epsilon))).add
      (differenceIntegrable.const_mul constant)).add (foreignSumIntegrable.const_mul (constant * epsilon))
  let returnPrepared := prepared.enlargeCap returnCapBound
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : |velocity time| ≤ majorant time := by
    have actual := returnEstimate count phase dipoleAngle returnPrepared path index nonterminal finish
      finishNonnegative finishBound radialSmall time inside
    with_reducible_and_instances
      dsimp only [velocity, majorant, epsilon, first, second, difference, foreign, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  refine ⟨dilationContinuous, velocityContinuous, velocityIntegrable, differenceIntegrable, foreignIntegrable, majorantIntegrable, ?_⟩
  intro time inside
  have history : dilation time = ∫ current in (0 : ℝ)..time, velocity current := by
    simpa only [dilation, velocity, first, second, prepared.referenceIdentity] using
      (physicalHistory prepared.toCascadeMaterialPreparedPair path index nonterminal time (subset inside)).2
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have prefixSet : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact prefixSubset
  have normHistory : |dilation time| ≤ ∫ current in (0 : ℝ)..time, |velocity current| := by
    rw [history]
    simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := velocity) inside.1
  exact normHistory.trans (intervalIntegral.integral_mono_on inside.1
    (velocityIntegrable.mono_set prefixSet) (majorantIntegrable.mono_set prefixSet)
    (fun current member => pointwise current (prefixSubset member)))

end EulerNonuniqueness.Paper
