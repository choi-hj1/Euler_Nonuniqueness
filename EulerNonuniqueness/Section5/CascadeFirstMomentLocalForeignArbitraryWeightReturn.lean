import EulerNonuniqueness.Section5.CascadePrehitFirstMomentLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeFirstMomentArbitraryWeight
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeForeignCoefficientSeriesContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem weighted_firstMoment_local_foreign_arbitrary_weight
    {center raw difference defect moment : ℝ → ℝ} {foreign : Fin 4 → ℝ → ℝ}
    {finish weight constant strain epsilon : ℝ}
    (ordered : 0 ≤ finish) (weightPositive : 0 < weight)
    (centerIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * center time) volume 0 finish)
    (rawIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * raw time) volume 0 finish)
    (differenceIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish)
    (foreignIntegrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish)
    (defectIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * defect time) volume 0 finish)
    (pointwise : ∀ time ∈ Icc 0 finish,
      defect time ≤ constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))
    (history : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) ≤
      (2 / weight) * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) :
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) ≤
      2 * constant * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
        epsilon * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
          ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time)) := by
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch, foreign patch time) volume 0 finish := by
    simp_rw [Finset.mul_sum]
    simpa only [Finset.sum_apply] using
      (IntervalIntegrable.sum Finset.univ (f := fun (patch : Fin 4) (time : ℝ) =>
        Real.exp (-weight * time) * foreign patch time) (fun patch _ => foreignIntegrable patch))
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))) volume 0 finish := by
    have actual := ((centerIntegrable.const_mul (constant * strain)).add
      (differenceIntegrable.const_mul constant)).add
      (((rawIntegrable.const_mul strain).add foreignSumIntegrable).const_mul (constant * epsilon))
    convert actual using 1
    ext time
    ring
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered defectIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (constant * strain * center time + constant * difference time +
        constant * epsilon * (strain * raw time + ∑ patch, foreign patch time))) =
      constant * strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * (strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
        ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time) := by
    have integrandIdentity (time : ℝ) : Real.exp (-weight * time) *
        (constant * strain * center time + constant * difference time +
          constant * epsilon * (strain * raw time + ∑ patch, foreign patch time)) =
        constant * strain * (Real.exp (-weight * time) * center time) +
          constant * (Real.exp (-weight * time) * difference time) +
          constant * epsilon * (strain * (Real.exp (-weight * time) * raw time) +
            Real.exp (-weight * time) * ∑ patch, foreign patch time) := by ring
    simp_rw [integrandIdentity]
    rw [intervalIntegral.integral_add
        ((centerIntegrable.const_mul (constant * strain)).add (differenceIntegrable.const_mul constant))
        (((rawIntegrable.const_mul strain).add foreignSumIntegrable).const_mul (constant * epsilon)),
      intervalIntegral.integral_add (centerIntegrable.const_mul (constant * strain))
        (differenceIntegrable.const_mul constant)]
    simp only [intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_add (rawIntegrable.const_mul strain) foreignSumIntegrable]
    simp only [intervalIntegral.integral_const_mul]
    congr 2
    congr 1
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => foreignIntegrable patch)
  have multiplied := mul_le_mul_of_nonneg_left history weightPositive.le
  have cancellation : weight * (2 / weight) = 2 := by field_simp
  rw [← mul_assoc, cancellation] at multiplied
  have actual := multiplied.trans (mul_le_mul_of_nonneg_left (comparison.trans_eq identity) (by norm_num : (0 : ℝ) ≤ 2))
  convert actual using 1; ring

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_firstMoment_local_foreign_arbitrary_weight_return :
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
    ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (index.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let radius := factor / 39321600 * changed.location (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
    IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish ∧
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) volume 0 finish ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) ≤
    2 * constant * (changed.strain *
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      epsilon * (changed.strain * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
          ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time)) := by
  obtain ⟨pointwiseCap, pointwisePositive, pointwiseFactory⟩ :=
    exists_uniform_actual_prehit_firstMoment_local_foreign_return
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min pointwiseCap continuityCap
  have capPositive : 0 < rawCap := lt_min pointwisePositive continuityPositive
  have pointwiseCapBound : rawCap ≤ pointwiseCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, pointwiseParameters⟩ := pointwiseFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [pointwiseParameters scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    scales.eventually_cascade_firstMoment_arbitrary_weight_source_defect amplitudePositive ratioBound alphaPositive,
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne]
    with frequency pointwiseEstimate historyEstimate seriesEstimate
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall weight weightBound
  dsimp only
  simp only [prepared.referenceIdentity]
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let center := fun time => prepared.rawSourceCenteredState time index
  let raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
  let defect := relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index
  let curve := relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index
  have weightPositive : 0 < weight :=
    (zero_lt_one.trans_le (historyEstimate.1 (index.val + 1)).1).trans_le weightBound
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ =>
      ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have centerIntegrable := (exponential.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawIntegrable := (exponential.continuousOn.mul rawContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have radiusNonnegative : 0 ≤ radius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le
  have radiusSmall : radius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have numeric : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorOne]
    have multiplied := mul_le_mul_of_nonneg_right numeric (changed.location_pos (index.val + 1)).le
    simpa only [radius, div_eq_mul_inv, one_mul, mul_comm] using multiplied
  have actualSeries := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index radius radiusNonnegative radiusSmall
  dsimp only at actualSeries
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := actualSeries.2.2.mono subset
  have foreignContinuous (patch : Fin 4) : ContinuousOn (foreign patch) (Icc 0 finish) :=
    (actualSeries.1 patch).2.mono subset
  have differenceIntegrable := (exponential.continuousOn.mul differenceContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have foreignIntegrable (patch : Fin 4) :=
    (exponential.continuousOn.mul (foreignContinuous patch)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have actualHistory := historyEstimate.2 prepared.toCascadeMaterialPreparedPair path index nonterminal finish finishNonnegative finishBound weight weightBound
  simp only [prepared.referenceIdentity] at actualHistory
  have momentIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖curve time‖) volume 0 finish := actualHistory.1
  have defectIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * defect time) volume 0 finish := actualHistory.2.1
  have centerCapInvariant : (prepared.enlargeCap pointwiseCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant : (prepared.enlargeCap pointwiseCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      defect time ≤ constant * changed.strain * center time + constant * difference time +
        constant * epsilon * (changed.strain * raw time + ∑ patch, foreign patch time) := by
    have actual := pointwiseEstimate count phase dipoleAngle (prepared.enlargeCap pointwiseCapBound) path index nonterminal
      finish finishNonnegative finishBound radialSmall time inside
    dsimp only at actual
    simp only [centerCapInvariant, rawCapInvariant] at actual
    exact actual
  refine ⟨differenceIntegrable, foreignIntegrable, centerIntegrable, rawIntegrable, momentIntegrable, ?_⟩
  exact weighted_firstMoment_local_foreign_arbitrary_weight finishNonnegative weightPositive centerIntegrable rawIntegrable
    differenceIntegrable foreignIntegrable defectIntegrable pointwise actualHistory.2.2

end EulerNonuniqueness.Paper

