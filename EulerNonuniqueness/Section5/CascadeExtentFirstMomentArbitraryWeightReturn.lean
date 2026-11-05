import EulerNonuniqueness.Section5.CascadeExtentFirstMomentLocalForeignRate
import EulerNonuniqueness.Section5.CascadeFirstMomentArbitraryWeight
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadeForeignCoefficientSeriesContinuity
import EulerNonuniqueness.Section6.SourcePacketInitialNeutral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_firstMoment_arbitrary_weight_return :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ extentFactor ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop,
    (∀ index : ℕ,
      1 ≤ ({scales with frequency := frequency} : Scales).omega index ∧
      2 * (96 / Real.pi * (2304 * ({scales with frequency := frequency} : Scales).strain)) ≤
        ({scales with frequency := frequency} : Scales).omega index) ∧
    ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ, ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ finish : ℝ, 0 ≤ finish → finish ≤ path.stop →
    (∀ time ∈ Icc 0 finish, ∀ patch,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
          extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
    (∀ time ∈ Icc 0 finish, ∀ patch,
      ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
          extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
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
    let curve := relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index
    let defect := relativeFirstMomentSourceDefect changed first.patchMotion prepared.reference index
    let forcing := fun time => changed.strain * prepared.rawSourceCenteredState time index + difference time +
      epsilon * (changed.strain * ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch +
        ∑ patch : Fin 4, foreign patch time)
    curve 0 = 0 ∧ ContinuousOn curve (Icc 0 finish) ∧ ContinuousOn defect (Icc 0 finish) ∧
    ContinuousOn forcing (Icc 0 finish) ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * ‖curve time‖) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * defect time) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) * forcing time) volume 0 finish ∧
    (∀ time ∈ Icc 0 finish, defect time ≤ constant * extentFactor ^ 2 * forcing time) ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
      (2 / weight) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
      2 * constant * extentFactor ^ 2 * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * forcing time) := by
  obtain ⟨pointwiseCap, pointwisePositive, pointwiseFactory⟩ :=
    exists_uniform_actual_extent_firstMoment_local_foreign_rate
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  let rawCap := min pointwiseCap continuityCap
  have capPositive : 0 < rawCap := lt_min pointwisePositive continuityPositive
  have pointwiseCapBound : rawCap ≤ pointwiseCap := min_le_left _ _
  have continuityCapBound : rawCap ≤ continuityCap := min_le_right _ _
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, pointwiseParameters⟩ := pointwiseFactory factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro extentFactor extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [pointwiseParameters extentFactor extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne,
    scales.eventually_cascade_firstMoment_arbitrary_weight_source_defect amplitudePositive ratioBound alphaPositive,
    scales.eventually_cascade_foreign_coefficient_series_continuous amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorOne,
    eventually_gt_atTop (0 : ℝ)]
    with frequency pointwiseEstimate historyEstimate seriesEstimate frequencyPositive
  refine ⟨historyEstimate.1, ?_⟩
  intro count phase dipoleAngle shapeRadius monitor prepared path index finish finishNonnegative finishBound firstExtent secondExtent weight weightBound
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
  let curve := relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index
  let velocity := relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index
  let defect := relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index
  let forcing := fun time => changed.strain * center time + difference time +
    epsilon * (changed.strain * raw time + ∑ patch : Fin 4, foreign patch time)
  let coefficient := 96 / Real.pi * (2304 * changed.strain)
  have weightPositive : 0 < weight :=
    (zero_lt_one.trans_le (historyEstimate.1 (index.val + 1)).1).trans_le weightBound
  have driftWeight : 2 * coefficient ≤ weight := (historyEstimate.1 (index.val + 1)).2.trans weightBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp only [coefficient]; positivity
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have exponential : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) :=
    continuousOn_finset_sum _ (fun patch _ => ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have radiusNonnegative : 0 ≤ radius := mul_nonneg (div_nonneg factorPositive.le (by norm_num)) (changed.location_pos _).le
  have radiusSmall : radius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have numeric : factor / 39321600 ≤ 1 / (100000 * 96) := by linarith only [factorOne]
    have multiplied := mul_le_mul_of_nonneg_right numeric (changed.location_pos (index.val + 1)).le
    simpa only [radius, div_eq_mul_inv, one_mul, mul_comm] using multiplied
  have actualSeries := seriesEstimate count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index radius radiusNonnegative radiusSmall
  dsimp only at actualSeries
  have differenceContinuous : ContinuousOn difference (Icc 0 finish) := actualSeries.2.2.mono subset
  have foreignContinuous (patch : Fin 4) : ContinuousOn (foreign patch) (Icc 0 finish) := (actualSeries.1 patch).2.mono subset
  have forcingContinuous : ContinuousOn forcing (Icc 0 finish) :=
    ((continuousOn_const.mul centerContinuous).add differenceContinuous).add
      (continuousOn_const.mul ((continuousOn_const.mul rawContinuous).add
        (continuousOn_finset_sum _ (fun patch _ => foreignContinuous patch))))
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt curve (velocity time) time := by
    have actual := path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
    rw [prepared.referenceIdentity] at actual
    exact actual
  have curveContinuous : ContinuousOn curve (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) := by
    have actual := (path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index).mono subset
    rw [prepared.referenceIdentity] at actual
    exact actual
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuous_max.comp_continuousOn (continuousOn_const.prodMk
      (velocityContinuous.norm.sub (continuousOn_const.mul curveContinuous.norm)))
  have alternativeInitial := path.source_packet_initial_neutral amplitudePositive frequencyPositive ratioPositive
    (thresholdSmall.trans (by norm_num)) index
  have referenceInitial := (prepared.referenceWitness.evolution.reference_initial_center_and_asymmetry (by norm_num)
    amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index).2
  have initial : curve 0 = 0 := by
    dsimp only [curve, relativeNormalizedFirstMoment, first, second]
    rw [alternativeInitial, referenceInitial, sub_self, smul_zero]
  have centerCapInvariant : (prepared.enlargeCap pointwiseCapBound).rawSourceCenteredState = prepared.rawSourceCenteredState := by
    funext current source
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState]
  have rawCapInvariant : (prepared.enlargeCap pointwiseCapBound).rawSourceShapeBudget = prepared.rawSourceShapeBudget := by
    funext current source patch
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget]
  have forcingNonnegative (time : ℝ) : 0 ≤ forcing time := by
    have centerNonnegative : 0 ≤ center time := div_nonneg (norm_nonneg _) (changed.length_pos _).le
    have rawNonnegative : 0 ≤ raw time := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
    have differenceNonnegative : 0 ≤ difference time := tsum_nonneg (fun _ => norm_nonneg _)
    have foreignNonnegative : 0 ≤ ∑ patch : Fin 4, foreign patch time :=
      Finset.sum_nonneg fun patch _ => tsum_nonneg fun power => mul_nonneg (by positivity) (norm_nonneg _)
    dsimp only [forcing, epsilon]
    positivity
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : defect time ≤ constant * extentFactor ^ 2 * forcing time := by
    have actual := pointwiseEstimate count phase dipoleAngle (prepared.enlargeCap pointwiseCapBound) path index time (subset inside)
      (firstExtent time inside) (secondExtent time inside)
    dsimp only at actual
    simp only [centerCapInvariant, rawCapInvariant] at actual
    apply relativeFirstMomentSourceDefect_le_of_rate_bound changed first.patchMotion second.patchMotion index time
      (mul_nonneg (mul_nonneg constantNonnegative (sq_nonneg _)) (forcingNonnegative time))
    exact actual.2
  have majorantContinuous : ContinuousOn (fun time => coefficient * ‖curve time‖ + defect time) (Icc 0 finish) :=
    (continuousOn_const.mul curveContinuous.norm).add defectContinuous
  have weightedHistory := General.weighted_norm_of_interior_derivative_majorant finishNonnegative weightPositive
    curveContinuous initial majorantContinuous
    (fun time _ => add_nonneg (mul_nonneg coefficientNonnegative (norm_nonneg _)) (le_max_left _ _))
    (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩) (by
      intro time _
      have residual := le_max_right (0 : ℝ) (‖velocity time‖ - coefficient * ‖curve time‖)
      change ‖velocity time‖ ≤ coefficient * ‖curve time‖ + max 0 (‖velocity time‖ - coefficient * ‖curve time‖)
      linarith only [residual])
  have split := General.weighted_integral_three_term_identity
    (first := fun time => ‖curve time‖) (second := fun _ => (0 : ℝ)) (third := defect)
    (weight := weight) (coefficient := coefficient) finishNonnegative curveContinuous.norm continuousOn_const defectContinuous
  simp only [add_zero, mul_zero, intervalIntegral.integral_zero] at split
  rw [split] at weightedHistory
  have momentNonnegative : 0 ≤ ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖ :=
    intervalIntegral.integral_nonneg finishNonnegative (fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
  have multiplied := (le_div_iff₀ weightPositive).mp weightedHistory
  have coefficientBound := mul_le_mul_of_nonneg_right driftWeight momentNonnegative
  have absorbed : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
      2 * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) := by
    nlinarith only [multiplied, coefficientBound]
  have gain : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
      (2 / weight) * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) := by
    have divided : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ‖curve time‖) ≤
        (2 * ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * defect time) / weight := by
      apply (le_div_iff₀ weightPositive).mpr
      rw [mul_comm]
      exact absorbed
    exact divided.trans_eq (by ring)
  have momentIntegrable := (exponential.continuousOn.mul curveContinuous.norm).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have defectIntegrable := (exponential.continuousOn.mul defectContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have forcingIntegrable := (exponential.continuousOn.mul forcingContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have comparison := intervalIntegral.integral_mono_on finishNonnegative defectIntegrable
    (forcingIntegrable.const_mul (constant * extentFactor ^ 2)) (by
      intro time inside
      exact (mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le).trans_eq (by ring))
  rw [intervalIntegral.integral_const_mul] at comparison
  refine ⟨initial, curveContinuous, defectContinuous, forcingContinuous, momentIntegrable, defectIntegrable,
    forcingIntegrable, pointwise, gain, ?_⟩
  have scaled := mul_le_mul_of_nonneg_left comparison (by norm_num : (0 : ℝ) ≤ 2)
  exact absorbed.trans (scaled.trans_eq (by ring))

end EulerNonuniqueness.Paper
