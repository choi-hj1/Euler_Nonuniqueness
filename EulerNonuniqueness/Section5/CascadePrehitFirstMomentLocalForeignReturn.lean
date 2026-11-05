import EulerNonuniqueness.Section5.CascadePrehitFirstMomentSourceDefectReturn
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem firstMomentLocalForeign_scalar
    {strain hessian center difference epsilon memory scale centerConstant shapeConstant returnConstant amplitude defect : ℝ}
    (budgets series amplitudes : Fin 4 → ℝ)
    (strainNonnegative : 0 ≤ strain) (hessianSmall : hessian ≤ 1)
    (centerNonnegative : 0 ≤ center) (differenceNonnegative : 0 ≤ difference)
    (epsilonNonnegative : 0 ≤ epsilon) (memoryNonnegative : 0 ≤ memory) (scalePositive : 0 < scale)
    (centerConstantNonnegative : 0 ≤ centerConstant) (shapeConstantNonnegative : 0 ≤ shapeConstant)
    (returnConstantNonnegative : 0 ≤ returnConstant) (amplitudeNonnegative : 0 ≤ amplitude)
    (budgetNonnegative : ∀ patch, 0 ≤ budgets patch) (seriesNonnegative : ∀ patch, 0 ≤ series patch)
    (amplitudesBound : ∀ patch, amplitudes patch ≤ amplitude)
    (bound : defect ≤ max 0 (centerConstant * strain * center +
      (4 * memory * hessian + 36 / scale) * difference + returnConstant * epsilon *
        ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch))) :
    let constant := centerConstant + (4 * memory + 36 / scale) + returnConstant * (shapeConstant + amplitude)
    defect ≤ constant * strain * center + constant * difference +
      constant * epsilon * (strain * ∑ patch, budgets patch + ∑ patch, series patch) := by
  let constant := centerConstant + (4 * memory + 36 / scale) + returnConstant * (shapeConstant + amplitude)
  have coefficientNonnegative : 0 ≤ 4 * memory + 36 / scale := by positivity
  have coefficientBound : 4 * memory * hessian + 36 / scale ≤ 4 * memory + 36 / scale := by
    nlinarith [mul_le_mul_of_nonneg_left hessianSmall (show 0 ≤ 4 * memory by positivity)]
  have budgetSumNonnegative : 0 ≤ ∑ patch, budgets patch := Finset.sum_nonneg (fun patch _ => budgetNonnegative patch)
  have seriesSumNonnegative : 0 ≤ ∑ patch, series patch := Finset.sum_nonneg (fun patch _ => seriesNonnegative patch)
  have sumBound : (∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      (shapeConstant + amplitude) * (strain * ∑ patch, budgets patch + ∑ patch, series patch) := by
    have individual (patch : Fin 4) : series patch * amplitudes patch ≤ series patch * amplitude :=
      mul_le_mul_of_nonneg_left (amplitudesBound patch) (seriesNonnegative patch)
    have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => individual patch)
    rw [← Finset.sum_mul] at summed
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have first := mul_nonneg shapeConstantNonnegative seriesSumNonnegative
    have second := mul_nonneg amplitudeNonnegative (mul_nonneg strainNonnegative budgetSumNonnegative)
    nlinarith only [summed, first, second]
  have returnNonnegative : 0 ≤ returnConstant * (shapeConstant + amplitude) := by positivity
  have centerCoefficient : centerConstant ≤ constant := by dsimp only [constant]; linarith
  have differenceCoefficient : 4 * memory + 36 / scale ≤ constant := by dsimp only [constant]; linarith
  have returnCoefficient : returnConstant * (shapeConstant + amplitude) ≤ constant := by dsimp only [constant]; linarith
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  apply bound.trans
  apply max_le (by positivity)
  have centerBound := mul_le_mul_of_nonneg_right centerCoefficient (mul_nonneg strainNonnegative centerNonnegative)
  have differenceBound := mul_le_mul_of_nonneg_right (coefficientBound.trans differenceCoefficient) differenceNonnegative
  have returned := mul_le_mul_of_nonneg_left sumBound (mul_nonneg returnConstantNonnegative epsilonNonnegative)
  have returned' := mul_le_mul_of_nonneg_right returnCoefficient
    (mul_nonneg epsilonNonnegative (add_nonneg (mul_nonneg strainNonnegative budgetSumNonnegative) seriesSumNonnegative))
  have returnedBound : returnConstant * epsilon *
      (∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      constant * epsilon * (strain * ∑ patch, budgets patch + ∑ patch, series patch) := by
    apply returned.trans
    convert returned' using 1 <;> ring
  have combined := add_le_add (add_le_add centerBound differenceBound) returnedBound
  convert combined using 1 <;> ring

theorem exists_uniform_actual_prehit_firstMoment_local_foreign_return :
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
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily
    let second := prepared.referenceWitness.trajectory.movingFamily
    let radius := factor / 39321600 * changed.location (index.val + 1)
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
    let series := fun patch : Fin 4 => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖
    relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index time ≤
      constant * changed.strain * prepared.rawSourceCenteredState time index + constant * difference +
        constant * epsilon * (changed.strain * ∑ patch, prepared.rawSourceShapeBudget time index patch + ∑ patch, series patch) := by
  obtain ⟨memory, memoryOne, sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative, factory⟩ :=
    exists_uniform_actual_prehit_firstMoment_source_defect_return
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  let scale := factor / 39321600
  let centerConstant := (96 / Real.pi * 2304) * (24 / scale)
  let shapeConstant := (96 / Real.pi * 2304) / (factor / 8) ^ 2
  let returnConstant := sourceConstant / scale
  let amplitude := ‖diskPhysicalTransverseProjection‖ * sourceRadius
  let constant := centerConstant + (4 * memory + 36 / scale) + returnConstant * (shapeConstant + amplitude)
  have scalePositive : 0 < scale := by dsimp only [scale]; positivity
  have memoryNonnegative : 0 ≤ memory := by linarith
  refine ⟨constant, by dsimp only [constant, centerConstant, shapeConstant, returnConstant, amplitude]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorSmall,
    eventually_gt_atTop (0 : ℝ),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency estimate frequencyPositive hessianSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  obtain ⟨shapes, derivative, history, sourceBound⟩ := estimate count phase dipoleAngle prepared path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let radius := scale * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, finishBound, path.stopBound]⟩
  let comparisons := fun patch => prepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch)
  let budgets := fun patch => ((comparisons patch).source (finProdFinEquiv (index, patch))).spectralDifferenceBudget
  let series := fun patch => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (comparisons patch).firstReceiver radius (power + 1) time -
      (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (comparisons patch).secondReceiver radius (power + 1) time‖
  let amplitudes := fun patch => ‖diskPhysicalTransverseProjection ((comparisons patch).final (finProdFinEquiv (index, patch)))‖
  let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first.patchMotion index time radius power -
    quadrupoleExteriorCoefficient changed second.patchMotion index time radius power‖
  let centerState := ‖quadrupoleNormalizedCentroidOffsets first.patchMotion index time (changed.length (index.val + 1)) -
    quadrupoleNormalizedCentroidOffsets second.patchMotion index time (changed.length (index.val + 1))‖
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have amplitudesBound (patch : Fin 4) : amplitudes patch ≤ amplitude :=
    (diskPhysicalTransverseProjection.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (shapes patch (finProdFinEquiv (index, patch))).2.small.le (norm_nonneg _))
  have ratio24 : 24 * changed.location (index.val + 1) / radius = 24 / scale := by
    dsimp only [radius]; field_simp [scalePositive.ne', locationPositive.ne']; ring
  have ratio36 : 36 * changed.location (index.val + 1) / radius = 36 / scale := by
    dsimp only [radius]; field_simp [scalePositive.ne', locationPositive.ne']; ring
  have scalarBound : relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index time ≤
      max 0 (centerConstant * changed.strain * centerState + (4 * memory * changed.hessian + 36 / scale) * difference +
        returnConstant * epsilon * ∑ patch, (shapeConstant * changed.strain * budgets patch + series patch * amplitudes patch)) := by
    rw [← prepared.referenceIdentity]
    apply sourceBound.trans_eq
    congr 1
    dsimp only [comparisons, budgets, series, amplitudes, centerState, difference, epsilon, returnConstant]
    rw [prepared.referenceIdentity, ratio24, ratio36]
    dsimp only [centerConstant, shapeConstant, changed, radius, scale, first, second]
    ring
  have result := firstMomentLocalForeign_scalar
    (strain := changed.strain) (hessian := changed.hessian) (center := centerState) (difference := difference)
    (epsilon := epsilon) (memory := memory) (scale := scale) (centerConstant := centerConstant)
    (shapeConstant := shapeConstant) (returnConstant := returnConstant) (amplitude := amplitude)
    (defect := relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index time)
    budgets series amplitudes strainNonnegative hessianSmall.le
    (norm_nonneg _) (tsum_nonneg (fun _ => norm_nonneg _)) (by dsimp only [epsilon]; positivity)
    memoryNonnegative scalePositive (by dsimp only [centerConstant]; positivity)
    (by dsimp only [shapeConstant]; positivity) (by dsimp only [returnConstant]; positivity)
    (by dsimp only [amplitude]; positivity)
    (fun patch => ((comparisons patch).source (finProdFinEquiv (index, patch))).spectralDifferenceBudget_nonnegative)
    (fun _ => tsum_nonneg (fun _ => by positivity)) amplitudesBound scalarBound
  have budgetIdentity (patch : Fin 4) : budgets patch = prepared.rawSourceShapeBudget time index patch := by
    with_reducible_and_instances
      dsimp only [budgets, comparisons, MovingPatchSourceComparison.spectralDifferenceBudget,
        MovingPatchFamilySourceComparison.source, CascadeSourcePreparedPair.sourceComparison,
        CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate]
  have centerIdentity : centerState = prepared.rawSourceCenteredState time index := by
    let array := (fun patch => patchCentroid second.patchMotion time index patch - quadrupoleCenter second.patchMotion time index) -
      (fun patch => patchCentroid first.patchMotion time index patch - quadrupoleCenter first.patchMotion time index)
    have identity : quadrupoleNormalizedCentroidOffsets first.patchMotion index time (changed.length (index.val + 1)) -
        quadrupoleNormalizedCentroidOffsets second.patchMotion index time (changed.length (index.val + 1)) =
        -(changed.length (index.val + 1))⁻¹ • array := by
      funext patch
      simp only [quadrupoleNormalizedCentroidOffsets, Pi.sub_apply, Pi.smul_apply, array, Complex.real_smul,
        Complex.ofReal_neg, Complex.ofReal_inv]
      ring
    dsimp only [centerState]
    rw [identity, norm_smul, Real.norm_eq_abs, abs_neg, abs_inv, abs_of_pos lengthPositive]
    change _ = ‖array‖ / changed.length (index.val + 1)
    ring
  have seriesIdentity (patch : Fin 4) : series patch = ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
      ‖first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid first.patchMotion current index patch) radius (power + 1) time -
        second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
          (fun current => patchCentroid second.patchMotion current index patch) radius (power + 1) time‖ := by
    apply tsum_congr
    intro power
    have referenceCenter : (prepared.referenceWitness.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index patch :=
      prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    have alternativeCenter : (prepared.trajectory.movingFamily.patch (finProdFinEquiv (index, patch))).center time =
        patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch :=
      prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside index patch
    dsimp only [series, comparisons, CascadeSourcePreparedPair.sourceComparison,
      FiniteMovingPatchFamily.exteriorTaylorCoefficient, first, second]
    rw [referenceCenter, alternativeCenter]
    rw [norm_sub_rev]
  change relativeFirstMomentSourceDefect changed first.patchMotion second.patchMotion index time ≤
    constant * changed.strain * centerState + constant * difference +
      constant * epsilon * (changed.strain * ∑ patch, budgets patch + ∑ patch, series patch) at result
  rw [centerIdentity] at result
  simp_rw [budgetIdentity, seriesIdentity] at result
  exact result

end EulerNonuniqueness.Paper
