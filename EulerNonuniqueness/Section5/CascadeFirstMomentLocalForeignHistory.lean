import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignWeightedReturn
import EulerNonuniqueness.General.IntegratedCoefficientGronwall

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

theorem exists_uniform_actual_firstMoment_local_foreign_history :
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
    IntervalIntegrable difference volume 0 finish ∧
    (∀ patch : Fin 4, IntervalIntegrable (foreign patch) volume 0 finish) ∧
    ∀ time ∈ Icc 0 finish,
      ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ ≤
        constant * ∫ current in (0 : ℝ)..time,
          changed.strain * prepared.rawSourceCenteredState current index + difference current +
            epsilon * (changed.strain * (∑ patch : Fin 4, prepared.rawSourceShapeBudget current index patch) +
              ∑ patch : Fin 4, foreign patch current) := by
  obtain ⟨pointCap, pointPositive, pointFactory⟩ := exists_uniform_actual_prehit_firstMoment_local_foreign_return
  obtain ⟨integrabilityCap, integrabilityPositive, integrabilityFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_weighted_return
  let rawCap := min pointCap integrabilityCap
  have capPositive : 0 < rawCap := lt_min pointPositive integrabilityPositive
  have pointCapBound : rawCap ≤ pointCap := min_le_left _ _
  have integrabilityCapBound : rawCap ≤ integrabilityCap := min_le_right _ _
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨pointConstant, pointNonnegative, points⟩ := pointFactory factorPositive factorSmall
  obtain ⟨integrabilityConstant, integrabilityNonnegative, integrabilities⟩ := integrabilityFactory factorPositive factorSmall
  refine ⟨Real.exp 1 * pointConstant, mul_nonneg (Real.exp_pos _).le pointNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  have selfRateTendsto : Tendsto (fun frequency : ℝ => (96 / Real.pi : ℝ) *
      (2304 * ({scales with frequency := frequency} : Scales).strain)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_assoc] using (scales.strain_tendsto_zero ratioBound alphaPositive).const_mul ((96 / Real.pi : ℝ) * 2304)
  filter_upwards [points scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    integrabilities scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne,
    selfRateTendsto.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_gt_atTop (0 : ℝ)] with frequency pointEstimate integrabilityEstimate selfRateSmall frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let moment := relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index
  let velocity := relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index
  let rate := (96 / Real.pi : ℝ) * (2304 * changed.strain)
  let defect := relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index
  let difference := fun time => ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
  let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
      second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
  let forcing := fun time => changed.strain * prepared.rawSourceCenteredState time index + difference time +
    epsilon * (changed.strain * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) + ∑ patch : Fin 4, foreign patch time)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have rateOne : rate ≤ 1 := selfRateSmall.le
  have derivative (time : ℝ) (inside : time ∈ Icc 0 finish) : HasDerivAt moment (velocity time) time := by
    simpa only [moment, velocity, first, second, prepared.referenceIdentity, relativeFirstMomentExternalVelocity] using
      path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index (subset inside)
  have momentContinuous : ContinuousOn moment (Icc 0 finish) :=
    fun time inside => (derivative time inside).continuousAt.continuousWithinAt
  have velocityContinuous : ContinuousOn velocity (Icc 0 finish) := by
    simpa only [velocity, first, second, prepared.referenceIdentity] using
      (path.relativeFirstMomentExternalVelocity_continuousOn amplitudePositive frequencyPositive ratioPositive index).mono subset
  have defectContinuous : ContinuousOn defect (Icc 0 finish) :=
    continuousOn_const.sup (velocityContinuous.norm.sub (continuousOn_const.mul momentContinuous.norm))
  let integrabilityPrepared := prepared.enlargeCap integrabilityCapBound
  obtain ⟨weightedDifference, weightedForeign, weightedCenter, weightedRaw, _, _⟩ :=
    integrabilityEstimate count phase dipoleAngle integrabilityPrepared path index nonterminal finish finishNonnegative finishBound radialSmall
  have differenceIntegrable : IntervalIntegrable difference volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedDifference
    simpa only [difference, radius, first, second, integrabilityPrepared, CascadeSourcePreparedPair.enlargeCap] using actual
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable (foreign patch) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight (weightedForeign patch)
    simpa only [foreign, radius, first, second, integrabilityPrepared, CascadeSourcePreparedPair.enlargeCap] using actual
  have centerIntegrable : IntervalIntegrable (fun time => prepared.rawSourceCenteredState time index) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedCenter
    with_reducible_and_instances
      dsimp only [integrabilityPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceCenteredState] at actual ⊢
      exact actual
  have rawIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish := by
    have actual := intervalIntegrable_of_exponential_weight weightedRaw
    with_reducible_and_instances
      dsimp only [integrabilityPrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  have foreignSumIntegrable : IntervalIntegrable (fun time => ∑ patch : Fin 4, foreign patch time) volume 0 finish := by
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (f := foreign) (fun patch _ => foreignIntegrable patch)
  have forcingIntegrable : IntervalIntegrable forcing volume 0 finish := by
    exact ((centerIntegrable.const_mul changed.strain).add differenceIntegrable).add
      (((rawIntegrable.const_mul changed.strain).add foreignSumIntegrable).const_mul epsilon)
  let pointPrepared := prepared.enlargeCap pointCapBound
  have defectBound (time : ℝ) (inside : time ∈ Icc 0 finish) : defect time ≤ pointConstant * forcing time := by
    have actual := pointEstimate count phase dipoleAngle pointPrepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
    have normalized : defect time ≤ pointConstant * changed.strain * prepared.rawSourceCenteredState time index +
        pointConstant * difference time + pointConstant * epsilon *
          (changed.strain * (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) + ∑ patch : Fin 4, foreign patch time) := by
      with_reducible_and_instances
        dsimp only [defect, difference, foreign, radius, first, second, epsilon, pointPrepared, CascadeSourcePreparedPair.enlargeCap,
          CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
        exact actual
    exact normalized.trans_eq (by dsimp only [forcing]; ring)
  have velocityBound (time : ℝ) : ‖velocity time‖ ≤ defect time + rate * ‖moment time‖ := by
    have bound := le_max_right (0 : ℝ) (‖velocity time‖ - rate * ‖moment time‖)
    change ‖velocity time‖ ≤ max 0 (‖velocity time‖ - rate * ‖moment time‖) + rate * ‖moment time‖
    linarith only [bound]
  have momentHistory (time : ℝ) (inside : time ∈ Icc 0 finish) :
      ‖moment time‖ ≤ ∫ current in (0 : ℝ)..time, ‖velocity current‖ := by
    have actual := path.relativeNormalizedFirstMoment_original_history amplitudePositive frequencyPositive ratioPositive index nonterminal (subset inside)
    rw [prepared.referenceIdentity] at actual
    change moment time = ∫ current in (0 : ℝ)..time, velocity current at actual
    rw [actual]
    exact intervalIntegral.norm_integral_le_integral_norm inside.1
  have preliminary (time : ℝ) (inside : time ∈ Icc 0 finish) : ‖moment time‖ ≤ (0 : ℝ) +
      ∫ current in (0 : ℝ)..time, defect current + rate * ‖moment current‖ := by
    rw [zero_add]
    apply (momentHistory time inside).trans
    have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
    exact intervalIntegral.integral_mono_on inside.1
      ((velocityContinuous.norm.mono prefixSubset).intervalIntegrable_of_Icc (μ := volume) inside.1)
      (((defectContinuous.add (continuousOn_const.mul momentContinuous.norm)).mono prefixSubset).intervalIntegrable_of_Icc (μ := volume) inside.1)
      (fun current _ => velocityBound current)
  have resolved := General.integral_gronwall_of_integrated_coefficient_on_Icc
    (trajectory := fun time => ‖moment time‖) (forcing := defect) (coefficient := fun _ => rate)
    momentContinuous.norm defectContinuous continuousOn_const finishNonnegative
    (fun _ _ => le_max_left _ _) (fun _ _ => rateNonnegative) preliminary
  refine ⟨differenceIntegrable, foreignIntegrable, ?_⟩
  intro time inside
  have prefixSubset : Icc (0 : ℝ) time ⊆ Icc 0 finish := Icc_subset_Icc le_rfl inside.2
  have prefixSet : uIcc (0 : ℝ) time ⊆ uIcc 0 finish := by
    rw [uIcc_of_le inside.1, uIcc_of_le finishNonnegative]
    exact prefixSubset
  have defectIntegrable := (defectContinuous.mono prefixSubset).intervalIntegrable_of_Icc (μ := volume) inside.1
  have comparison := intervalIntegral.integral_mono_on inside.1 defectIntegrable
    ((forcingIntegrable.mono_set prefixSet).const_mul pointConstant) (fun current member => defectBound current (prefixSubset member))
  rw [intervalIntegral.integral_const_mul] at comparison
  have coefficientIntegral : (∫ current in (0 : ℝ)..time, rate) ≤ 1 := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have upperTime : time ≤ 1 := inside.2.trans (finishBound.trans path.stopBound)
    nlinarith only [rateOne, rateNonnegative, inside.1, upperTime,
      mul_nonneg (sub_nonneg.mpr rateOne) inside.1]
  have defectNonnegative : 0 ≤ ∫ current in (0 : ℝ)..time, defect current :=
    intervalIntegral.integral_nonneg inside.1 (fun _ _ => le_max_left _ _)
  have exponentialBound := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr coefficientIntegral) defectNonnegative
  have result := (resolved time inside).trans (by simpa only [zero_add] using exponentialBound)
  have final := result.trans (mul_le_mul_of_nonneg_left comparison (Real.exp_pos 1).le)
  convert final using 1
  dsimp only [moment, first, second, forcing]
  ring

end EulerNonuniqueness.Paper
