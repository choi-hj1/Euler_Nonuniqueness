import EulerNonuniqueness.Section5.CascadePrehitCenterLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeCenterWeightedHistory
import EulerNonuniqueness.Section5.CascadeForeignPatchCoefficientIntegrability
import EulerNonuniqueness.Section5.CascadeActualMacroForeignVelocityAction
import EulerNonuniqueness.Section5.CascadeSourceStateContinuity
import EulerNonuniqueness.Section5.CascadePrehitFirstMomentRate
import EulerNonuniqueness.Section6.MovingPatchStrainMeasurability
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

open EulerNonuniqueness.Section6

theorem exists_uniform_actual_center_local_foreign_weighted_return :
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
    ∀ weight : ℝ, 0 < weight →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let location := changed.location (index.val + 1)
    let length := changed.length (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
    let patchRadius := factor / 39321600 * length
    let external := fun (patch : Fin 4) (time : ℝ) =>
      ‖biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch) -
        biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch)‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location)) volume 0 finish ∧
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * external patch time) volume 0 finish) ∧
    (∀ patch : Fin 4, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish) ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location)) ≤
      tolerance * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖) +
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      (∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * external patch time) / (4 * location) +
      constant * changed.omega (index.val + 1) * (length / location) * epsilon *
        ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * (length / location) * epsilon *
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
  obtain ⟨returnCap, returnPositive, returns⟩ := exists_uniform_actual_prehit_center_local_foreign_return
  obtain ⟨patchCap, patchPositive, patches⟩ := exists_uniform_actual_foreign_patch_coefficient_integrability
  obtain ⟨continuityCap, continuityPositive, stateContinuity⟩ := exists_uniform_actual_source_state_continuity
  obtain ⟨velocityRadius, velocityRadiusPositive, velocityCap, velocityPositive, velocityConstant, velocityNonnegative, velocities⟩ :=
    exists_uniform_actual_macro_foreign_velocity_action
  let rawCap := min returnCap (min patchCap (min continuityCap velocityCap))
  have capPositive : 0 < rawCap := lt_min returnPositive (lt_min patchPositive (lt_min continuityPositive velocityPositive))
  have returnCapBound : rawCap ≤ returnCap := min_le_left _ _
  have patchCapBound : rawCap ≤ patchCap := (min_le_right _ _).trans (min_le_left _ _)
  have continuityCapBound : rawCap ≤ continuityCap :=
    ((min_le_right returnCap _).trans (min_le_right patchCap _)).trans (min_le_left _ _)
  have velocityCapBound : rawCap ≤ velocityCap :=
    ((min_le_right returnCap _).trans (min_le_right patchCap _)).trans (min_le_right _ _)
  refine ⟨rawCap, capPositive, ?_⟩
  intro factor factorPositive factorSmall
  obtain ⟨constant, constantNonnegative, localFactory⟩ := returns factorPositive factorSmall
  refine ⟨constant, constantNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold
    referenceConstant tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [localFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne
      thresholdSmall referenceNonnegative tolerancePositive,
    patches scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne
      boundaryOne factorPositive factorOne,
    velocities scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative rootOne
      boundaryOne factorPositive factorOne,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    eventually_gt_atTop (0 : ℝ)] with frequency localEstimate patchEstimate velocityEstimate lengths frequencyPositive
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall weight weightPositive
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let location := changed.location (index.val + 1)
  let length := changed.length (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let patchRadius := factor / 39321600 * length
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
  let centerDifference := fun time => ‖quadrupoleCenter first.patchMotion time index - quadrupoleCenter second.patchMotion time index‖ / location
  let velocity := fun time => ‖prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity 1 index time‖ / location
  let macroEnvelope := fun time => ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  let majorantCoefficient := (50000 * (velocityConstant + 1) / location ^ 4) *
    (216360000 * changed.hessian + 576 * changed.strain)
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have locationPositive : 0 < location := changed.location_pos _
  have lengthPositive : 0 < length := changed.length_pos _
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have centerContinuous : ContinuousOn center (Icc 0 finish) :=
    (stateContinuity prepared capPositive continuityCapBound path index).2.1.mono subset
  have rawContinuous : ContinuousOn raw (Icc 0 finish) := continuousOn_finset_sum _ (fun patch _ =>
    ((stateContinuity prepared capPositive continuityCapBound path index).1 patch).mono subset)
  have macroContinuous : ContinuousOn macroEnvelope (Icc 0 finish) :=
    (continuousOn_pi.mpr (fun source => continuousOn_const.mul
      ((stateContinuity prepared capPositive continuityCapBound path source).2.2.2.mono subset))).norm
  have momentContinuous : ContinuousOn moment (Icc 0 finish) := by
    have actual : ContinuousOn (fun time => relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time) (Icc 0 finish) :=
      fun time inside => (path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index
        (subset inside)).continuousAt.continuousWithinAt
    rw [prepared.referenceIdentity] at actual
    exact actual.norm
  have centerDifferenceContinuous : Continuous centerDifference :=
    ((first.quadrupoleCenter_continuous index).sub (second.quadrupoleCenter_continuous index)).norm.div_const _
  have velocityContinuous : Continuous velocity :=
    ((prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity_continuous 0 index).sub
      (prepared.toCascadeMaterialPreparedPair.pairedCenterVelocity_continuous 1 index)).norm.div_const _
  have centerIntegrable := (weightContinuous.continuousOn.mul centerContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have rawIntegrable := (weightContinuous.continuousOn.mul rawContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have momentIntegrable := (weightContinuous.continuousOn.mul momentContinuous).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have centerDifferenceIntegrable := (weightContinuous.mul centerDifferenceContinuous).intervalIntegrable (μ := volume) 0 finish
  have velocityIntegrable := (weightContinuous.mul velocityContinuous).intervalIntegrable (μ := volume) 0 finish
  have fieldMeasurable (family : FiniteMovingPatchFamily (count * 4))
      (densities : ∀ source patch, family.density (finProdFinEquiv (source, patch)) =
        patchSign patch * changed.amplitude * changed.omega (source.val + 1) ^ 4) (patch : Fin 4) :
      Measurable (fun time => biotSavart (externalPatchVorticity changed family.patchMotion time index)
        (patchCentroid family.patchMotion time index patch)) := by
    have sourceMeasurable : Measurable (fun point : ℝ × ℂ => externalPatchVorticity changed family.patchMotion point.1 index point.2) := by
      change Measurable (fun point : ℝ × ℂ => ∑ source ∈ Finset.univ.erase index,
        quadrupoleDensity changed family.patchMotion point.1 source point.2)
      exact Finset.measurable_sum _ (fun source _ => family.measurable_quadrupoleDensity changed densities source)
    have joint := measurable_biotSavart_of_measurable_vorticity (Parameter := ℝ)
      (vorticity := fun time => externalPatchVorticity changed family.patchMotion time index) sourceMeasurable
    have parameters := measurable_id.prodMk (family.patchCentroid_continuous index patch).measurable
    with_reducible_and_instances
      simpa only [Function.comp_def, id_eq] using joint.comp parameters
  have externalMeasurable (patch : Fin 4) : Measurable (external patch) :=
    ((fieldMeasurable first prepared.densityIdentity patch).sub
      (fieldMeasurable second prepared.referenceWitness.densityIdentity patch)).norm
  have externalBound (patch : Fin 4) (time : ℝ) (inside : time ∈ Icc 0 finish) :
      external patch time ≤ location * majorantCoefficient * macroEnvelope time := by
    let enlarged := prepared.enlargeCap velocityCapBound
    obtain ⟨shapes, bound⟩ := velocityEstimate count phase dipoleAngle enlarged path (subset inside) (index, patch)
    dsimp only at bound
    have firstIdentity : enlarged.trajectory.movingFamily = first := by
      dsimp only [enlarged, CascadeSourcePreparedPair.enlargeCap, first]
    have secondIdentity : enlarged.referenceWitness.trajectory.movingFamily = second := by
      dsimp only [enlarged, CascadeSourcePreparedPair.enlargeCap, second]
    have stateIdentity (source : Fin count) : enlarged.macroSourceState time source = prepared.macroSourceState time source := by
      with_reducible_and_instances
        dsimp only [enlarged, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.macroSourceState]
    rw [firstIdentity, secondIdentity] at bound
    simp_rw [stateIdentity] at bound
    have normIdentity : ‖biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch) -
        biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch)‖ = external patch time :=
      norm_sub_rev _ _
    change location ^ 4 *
      (‖biotSavart (externalPatchVorticity changed second.patchMotion time index) (patchCentroid second.patchMotion time index patch) -
        biotSavart (externalPatchVorticity changed first.patchMotion time index) (patchCentroid first.patchMotion time index patch)‖ / location) ≤
      (50000 * (velocityConstant + 1)) * (216360000 * changed.hessian + 576 * changed.strain) * macroEnvelope time at bound
    rw [normIdentity] at bound
    have normalized : external patch time / location ≤ majorantCoefficient * macroEnvelope time := by
      calc
        _ ≤ ((50000 * (velocityConstant + 1)) * (216360000 * changed.hessian + 576 * changed.strain) * macroEnvelope time) / location ^ 4 :=
          (le_div_iff₀ (pow_pos locationPositive 4)).mpr (by simpa only [mul_comm] using bound)
        _ = _ := by dsimp only [majorantCoefficient]; ring
    exact ((div_le_iff₀ locationPositive).mp normalized).trans_eq (by ring)
  have externalIntegrable (patch : Fin 4) : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * external patch time) volume 0 finish := by
    have majorantIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
        (location * majorantCoefficient * macroEnvelope time)) volume 0 finish :=
      (weightContinuous.continuousOn.mul (continuousOn_const.mul macroContinuous)).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
    exact majorantIntegrable.mono_fun' (weightContinuous.measurable.mul (externalMeasurable patch)).aestronglyMeasurable.restrict (by
      rw [uIoc_of_le finishNonnegative]
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with time inside
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))]
      exact mul_le_mul_of_nonneg_left (externalBound patch time ⟨inside.1.le, inside.2⟩) (Real.exp_pos _).le)
  have patchRadiusNonnegative : 0 ≤ patchRadius := by dsimp only [patchRadius]; positivity
  have patchRadiusSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have lengthBound := (lengths (index.val + 1)).le
    change length ≤ 1 * location at lengthBound
    change patchRadius ≤ location / (100000 * 96)
    have scaled := mul_le_mul_of_nonneg_right factorOne lengthPositive.le
    dsimp only [patchRadius]
    nlinarith only [lengthBound, scaled, locationPositive]
  have foreignIntegrable (patch : Fin 4) : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish := by
    have actual := patchEstimate count phase dipoleAngle (prepared.enlargeCap patchCapBound) path (index, patch)
      patchRadius patchRadiusNonnegative patchRadiusSmall finish finishNonnegative finishBound weight
    exact actual.2.2
  have externalSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch : Fin 4, external patch time) volume 0 finish := by
    simp_rw [Finset.mul_sum]
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun patch _ => externalIntegrable patch)
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch : Fin 4, foreign patch time) volume 0 finish := by
    simp_rw [Finset.mul_sum]
    simpa only [Finset.sum_apply] using IntervalIntegrable.sum Finset.univ (fun patch _ => foreignIntegrable patch)
  let upper := fun time => tolerance * (moment time + center time) + (∑ patch : Fin 4, external patch time) / (4 * location) +
    constant * changed.omega (index.val + 1) * (length / location) * epsilon * (center time + raw time) +
    constant * (length / location) * epsilon * ∑ patch : Fin 4, foreign patch time
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * upper time) volume 0 finish := by
    have actual := (((momentIntegrable.add centerIntegrable).const_mul tolerance).add
      (externalSumIntegrable.div_const (4 * location))).add
      ((centerIntegrable.add rawIntegrable).const_mul (constant * changed.omega (index.val + 1) * (length / location) * epsilon))
    have actual := actual.add (foreignSumIntegrable.const_mul (constant * (length / location) * epsilon))
    convert actual using 1
    ext time
    dsimp only [upper]
    ring
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) : velocity time ≤ upper time := by
    have actual := localEstimate count phase dipoleAngle (prepared.enlargeCap returnCapBound) path index nonterminal
      finish finishNonnegative finishBound radialSmall time inside
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.enlargeCap, upper, moment, center, raw, foreign, external, velocity,
        first, second, changed, epsilon, patchRadius, location, length,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  have comparison := intervalIntegral.integral_mono_on (μ := volume) finishNonnegative velocityIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have history := path.relative_center_weighted_history index nonterminal finishNonnegative finishBound weightPositive
  rw [prepared.referenceIdentity] at history
  have weightedHistory : weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * centerDifference time) ≤
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * velocity time := by
    have actual := (le_div_iff₀ weightPositive).mp history
    simpa only [mul_comm] using actual
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * upper time) =
      tolerance * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
        ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      (∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * external patch time) / (4 * location) +
      constant * changed.omega (index.val + 1) * (length / location) * epsilon *
        ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
          ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
      constant * (length / location) * epsilon *
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
    have integrandIdentity (time : ℝ) : Real.exp (-weight * time) * upper time =
        tolerance * (Real.exp (-weight * time) * moment time + Real.exp (-weight * time) * center time) +
        (Real.exp (-weight * time) * ∑ patch : Fin 4, external patch time) / (4 * location) +
        (constant * changed.omega (index.val + 1) * (length / location) * epsilon) *
          (Real.exp (-weight * time) * center time + Real.exp (-weight * time) * raw time) +
        (constant * (length / location) * epsilon) * (Real.exp (-weight * time) * ∑ patch : Fin 4, foreign patch time) := by
      dsimp only [upper]
      ring
    simp_rw [integrandIdentity]
    rw [intervalIntegral.integral_add
        ((((momentIntegrable.add centerIntegrable).const_mul tolerance).add (externalSumIntegrable.div_const (4 * location))).add
          ((centerIntegrable.add rawIntegrable).const_mul _)) (foreignSumIntegrable.const_mul _),
      intervalIntegral.integral_add
        (((momentIntegrable.add centerIntegrable).const_mul tolerance).add (externalSumIntegrable.div_const (4 * location)))
        ((centerIntegrable.add rawIntegrable).const_mul _),
      intervalIntegral.integral_add ((momentIntegrable.add centerIntegrable).const_mul tolerance)
        (externalSumIntegrable.div_const (4 * location))]
    simp only [intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
    rw [intervalIntegral.integral_add momentIntegrable centerIntegrable, intervalIntegral.integral_add centerIntegrable rawIntegrable]
    have externalIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ∑ patch : Fin 4, external patch time) =
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * external patch time := by
      simp_rw [Finset.mul_sum]
      exact intervalIntegral.integral_finset_sum (fun patch _ => externalIntegrable patch)
    have foreignIdentity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * ∑ patch : Fin 4, foreign patch time) =
        ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
      simp_rw [Finset.mul_sum]
      exact intervalIntegral.integral_finset_sum (fun patch _ => foreignIntegrable patch)
    rw [externalIdentity, foreignIdentity]
  exact ⟨centerDifferenceIntegrable, externalIntegrable, foreignIntegrable,
    weightedHistory.trans (comparison.trans_eq identity)⟩

end EulerNonuniqueness.Paper
