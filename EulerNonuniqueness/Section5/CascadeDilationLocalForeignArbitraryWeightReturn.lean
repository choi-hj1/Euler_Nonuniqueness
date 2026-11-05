import EulerNonuniqueness.Section5.CascadePrehitDilationLocalForeignReturn
import EulerNonuniqueness.Section5.CascadeDilationClosedPhysicalHistory
import EulerNonuniqueness.Section5.CascadeFirstMomentLocalForeignArbitraryWeightReturn
import EulerNonuniqueness.Section5.CascadeForeignPatchCoefficientIntegrability
import EulerNonuniqueness.General.TriangularNeutralWeightedHistory

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

private theorem weighted_dilation_local_foreign_arbitrary_weight
    {dilation velocity moment center raw difference : ℝ → ℝ} {foreign : Fin 4 → ℝ → ℝ}
    {finish weight tolerance constant strain omega epsilon : ℝ}
    (ordered : 0 ≤ finish) (weightPositive : 0 < weight)
    (momentIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * moment time) volume 0 finish)
    (centerIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * center time) volume 0 finish)
    (rawIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * raw time) volume 0 finish)
    (differenceIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * difference time) volume 0 finish)
    (foreignIntegrable : ∀ patch, IntervalIntegrable (fun time => Real.exp (-weight * time) * foreign patch time) volume 0 finish)
    (velocityIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) * |velocity time|) volume 0 finish)
    (pointwise : ∀ time ∈ Icc 0 finish,
      |velocity time| ≤ tolerance * moment time + (tolerance + constant * strain + constant * omega * epsilon) * center time +
        constant * omega * epsilon * raw time + constant * difference time + constant * epsilon * ∑ patch, foreign patch time)
    (history : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |dilation time|) ≤
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |velocity time|) / weight) :
    let bound :=
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
      (tolerance + constant * strain + constant * omega * epsilon) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      constant * omega * epsilon * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |velocity time|) ≤ bound ∧
      weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |dilation time|) ≤ bound := by
  dsimp only
  have foreignSumIntegrable : IntervalIntegrable
      (fun time => Real.exp (-weight * time) * ∑ patch, foreign patch time) volume 0 finish := by
    have finite := IntervalIntegrable.sum (μ := volume) (a := (0 : ℝ)) (b := finish) Finset.univ
      (f := fun (patch : Fin 4) (time : ℝ) => Real.exp (-weight * time) * foreign patch time)
      (fun patch _ => foreignIntegrable patch)
    simpa only [Finset.mul_sum] using finite
  let centerCoefficient := tolerance + constant * strain + constant * omega * epsilon
  have upperIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      (tolerance * moment time + centerCoefficient * center time + constant * omega * epsilon * raw time +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time)) volume 0 finish := by
    convert ((((momentIntegrable.const_mul tolerance).add (centerIntegrable.const_mul centerCoefficient)).add
      (rawIntegrable.const_mul (constant * omega * epsilon))).add (differenceIntegrable.const_mul constant)).add
      (foreignSumIntegrable.const_mul (constant * epsilon)) using 1
    ext time
    ring
  have comparison := intervalIntegral.integral_mono_on (μ := volume) ordered velocityIntegrable upperIntegrable
    (fun time inside => mul_le_mul_of_nonneg_left (pointwise time inside) (Real.exp_pos _).le)
  have identity : (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      (tolerance * moment time + centerCoefficient * center time + constant * omega * epsilon * raw time +
        constant * difference time + constant * epsilon * ∑ patch, foreign patch time)) =
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * moment time) +
      centerCoefficient * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * center time) +
      constant * omega * epsilon * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * raw time) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * ∑ patch, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time := by
    simp_rw [mul_add, mul_left_comm (Real.exp _) tolerance, mul_left_comm (Real.exp _) centerCoefficient,
      mul_left_comm (Real.exp _) (constant * omega * epsilon), mul_left_comm (Real.exp _) constant,
      mul_left_comm (Real.exp _) (constant * epsilon)]
    rw [intervalIntegral.integral_add
        ((((momentIntegrable.const_mul tolerance).add (centerIntegrable.const_mul centerCoefficient)).add
          (rawIntegrable.const_mul (constant * omega * epsilon))).add (differenceIntegrable.const_mul constant))
        (foreignSumIntegrable.const_mul (constant * epsilon)),
      intervalIntegral.integral_add
        (((momentIntegrable.const_mul tolerance).add (centerIntegrable.const_mul centerCoefficient)).add
          (rawIntegrable.const_mul (constant * omega * epsilon))) (differenceIntegrable.const_mul constant),
      intervalIntegral.integral_add ((momentIntegrable.const_mul tolerance).add (centerIntegrable.const_mul centerCoefficient))
        (rawIntegrable.const_mul (constant * omega * epsilon)),
      intervalIntegral.integral_add (momentIntegrable.const_mul tolerance) (centerIntegrable.const_mul centerCoefficient)]
    simp only [intervalIntegral.integral_const_mul]
    congr 2
    simp_rw [Finset.mul_sum]
    exact intervalIntegral.integral_finset_sum (fun patch _ => foreignIntegrable patch)
  have multiplied := mul_le_mul_of_nonneg_left history weightPositive.le
  have cancellation : weight * ((∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |velocity time|) / weight) =
      ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |velocity time| := by field_simp [weightPositive.ne']
  rw [cancellation] at multiplied
  exact ⟨comparison.trans_eq identity, multiplied.trans (comparison.trans_eq identity)⟩

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_prehit_dilation_local_foreign_arbitrary_weight_return :
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
    ∀ weight : ℝ, ({scales with frequency := frequency} : Scales).omega (index.val + 1) ≤ weight →
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let centerRadius := factor / 39321600 * changed.location (index.val + 1)
    let patchRadius := factor / 39321600 * changed.length (index.val + 1)
    let dilation := fun time => (diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
      changed.length (index.val + 1) ^ 2
    let difference := fun time => ∑' power : ℕ,
      ‖quadrupoleExteriorCoefficient changed first.patchMotion index time centerRadius power -
        quadrupoleExteriorCoefficient changed second.patchMotion index time centerRadius power‖
    let foreign := fun (patch : Fin 4) (time : ℝ) => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) patchRadius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) patchRadius (power + 1) time‖
    let bound :=
      tolerance * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖) +
      (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) * epsilon) *
        (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * prepared.rawSourceCenteredState time index) +
      constant * changed.omega (index.val + 1) * epsilon * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
      constant * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * difference time) +
      constant * epsilon * ∑ patch : Fin 4, ∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * foreign patch time
    IntervalIntegrable (fun time => Real.exp (-weight * time) * |dilation time|) volume 0 finish ∧
    IntervalIntegrable (fun time => Real.exp (-weight * time) *
      |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|) volume 0 finish ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
      |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|) ≤ bound ∧
    weight * (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |dilation time|) ≤ bound ∧
    (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) * |dilation time|) ≤
      (∫ time in (0 : ℝ)..finish, Real.exp (-weight * time) *
        |relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index time|) / weight := by
  obtain ⟨returnCap, returnPositive, returnFactory⟩ := exists_uniform_actual_prehit_dilation_local_foreign_return
  obtain ⟨momentCap, momentPositive, momentFactory⟩ := exists_uniform_actual_firstMoment_local_foreign_arbitrary_weight_return
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
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall weight weightBound
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let dilation := fun time => (diagonalDifference first.patchMotion time index - diagonalDifference second.patchMotion time index) /
    changed.length (index.val + 1) ^ 2
  let velocity := relativeDilationPhysicalVelocity changed first.patchMotion second.patchMotion index
  let mechanical := fun time => (prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 0 index time -
    prepared.toCascadeMaterialPreparedPair.pairedDiagonalVelocity 1 index time) / changed.length (index.val + 1) ^ 2
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
  have subset : Icc (0 : ℝ) finish ⊆ Icc 0 path.stop := Icc_subset_Icc le_rfl finishBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have omegaPositive := changed.omega_pos frequencyPositive ratioPositive (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have weightPositive : 0 < weight := omegaPositive.trans_le weightBound
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
  have initial : dilation 0 = 0 := by
    dsimp only [dilation, first, second]
    rw [← prepared.referenceIdentity]
    have same : diagonalDifference prepared.trajectory.movingFamily.patchMotion 0 index = diagonalDifference prepared.reference 0 index := by
      simp only [diagonalDifference, positiveHalfDiagonal, negativeHalfDiagonal, prepared.toCascadeMaterialPreparedPair.nonterminal_initial_centroid index nonterminal]
    rw [same, sub_self, zero_div]
  have weightContinuous : Continuous (fun time : ℝ => Real.exp (-weight * time)) := by fun_prop
  have dilationIntegrable := (weightContinuous.continuousOn.mul dilationContinuous.abs).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  have velocityIntegrable := (weightContinuous.continuousOn.mul velocityContinuous.abs).intervalIntegrable_of_Icc (μ := volume) finishNonnegative
  let momentPrepared := prepared.enlargeCap momentCapBound
  obtain ⟨differenceIntegrable, _, centerIntegrable, rawIntegrable, momentIntegrable, _⟩ :=
    momentEstimate count phase dipoleAngle momentPrepared path index nonterminal finish finishNonnegative finishBound radialSmall weight weightBound
  change IntervalIntegrable (fun time => Real.exp (-weight * time) *
    ‖relativeNormalizedFirstMoment changed first.patchMotion prepared.reference index time‖) volume 0 finish at momentIntegrable
  rw [prepared.referenceIdentity] at momentIntegrable
  have literalCenterIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      prepared.rawSourceCenteredState time index) volume 0 finish := by
    with_reducible_and_instances
      dsimp only [momentPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState] at centerIntegrable ⊢
      exact centerIntegrable
  have literalRawIntegrable : IntervalIntegrable (fun time => Real.exp (-weight * time) *
      ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) volume 0 finish := by
    with_reducible_and_instances
      dsimp only [momentPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceShapeBudget] at rawIntegrable ⊢
      exact rawIntegrable
  let patchPrepared := prepared.enlargeCap patchCapBound
  let patchRadius := factor / 39321600 * changed.length (index.val + 1)
  have patchRadiusNonnegative : 0 ≤ patchRadius := by dsimp only [patchRadius]; positivity
  have patchRadiusSmall : patchRadius ≤ scales.location (index.val + 1) / (100000 * 96) := by
    have lengthBound := (lengths (index.val + 1)).le
    change changed.length (index.val + 1) ≤ 1 * changed.location (index.val + 1) at lengthBound
    dsimp only [patchRadius]
    have product := mul_le_mul_of_nonneg_left lengthBound (show 0 ≤ factor / 39321600 by positivity)
    have locationPositive := changed.location_pos (index.val + 1)
    change _ ≤ changed.location (index.val + 1) / (100000 * 96)
    nlinarith only [product, locationPositive, mul_nonneg (sub_nonneg.mpr factorSmall) locationPositive.le]
  have foreignIntegrable (patch : Fin 4) :=
    (patchEstimate count phase dipoleAngle patchPrepared path (index, patch) patchRadius patchRadiusNonnegative
      patchRadiusSmall finish finishNonnegative finishBound weight).2.2
  have history := General.weighted_norm_of_interior_derivative_majorant finishNonnegative weightPositive
    dilationContinuous initial velocityContinuous.abs (fun _ _ => abs_nonneg _)
    (fun time inside => derivative time ⟨inside.1.le, inside.2.le⟩)
    (fun _ _ => by simp only [Real.norm_eq_abs]; exact le_rfl)
  simp only [Real.norm_eq_abs] at history
  refine ⟨dilationIntegrable, velocityIntegrable, ?_⟩
  let returnPrepared := prepared.enlargeCap returnCapBound
  have pointwise (time : ℝ) (inside : time ∈ Icc 0 finish) :
      |velocity time| ≤ tolerance * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
        (tolerance + constant * changed.strain + constant * changed.omega (index.val + 1) *
          (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2)) * prepared.rawSourceCenteredState time index +
        constant * changed.omega (index.val + 1) * (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) *
          (∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch) +
        constant * difference time + constant * (changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2) *
          ∑ patch : Fin 4, foreign patch time := by
    have actual := returnEstimate count phase dipoleAngle returnPrepared path index nonterminal finish
      finishNonnegative finishBound radialSmall time inside
    with_reducible_and_instances
      dsimp only [velocity, first, second, difference, foreign, returnPrepared, CascadeSourcePreparedPair.enlargeCap,
        CascadeSourcePreparedPair.rawSourceCenteredState, CascadeSourcePreparedPair.rawSourceShapeBudget] at actual ⊢
      exact actual
  have bounds := weighted_dilation_local_foreign_arbitrary_weight (dilation := dilation) (velocity := velocity)
    (moment := fun time => ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖)
    (center := fun time => prepared.rawSourceCenteredState time index)
    (raw := fun time => ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch)
    (difference := difference) (foreign := foreign) (finish := finish) (weight := weight) (tolerance := tolerance)
    (constant := constant) (strain := changed.strain) (omega := changed.omega (index.val + 1))
    (epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2)
    finishNonnegative weightPositive momentIntegrable literalCenterIntegrable literalRawIntegrable
    differenceIntegrable foreignIntegrable velocityIntegrable pointwise history
  exact ⟨bounds.1, bounds.2, history⟩

end EulerNonuniqueness.Paper

