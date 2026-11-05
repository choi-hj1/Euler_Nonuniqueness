import EulerNonuniqueness.Section5.CascadeOwnLocalVirtualSourceReturn
import EulerNonuniqueness.Section5.CascadeActualPatchMacroVirtualCoefficientAction
import EulerNonuniqueness.Section5.CascadeActualCentroidErrorArrayReturn
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity
import EulerNonuniqueness.Section6.MovingErasedOwnForeignSeries

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem centroidBudgetLocalForeignReturn_scalar
    {omega center raw amplitude own foreign receiver reference sourceCenter sourceShape sourcePart selfBudget difference actualReference : ℝ}
    (omegaPositive : 0 < omega) (centerNonnegative : 0 ≤ center) (rawNonnegative : 0 ≤ raw)
    (amplitudeNonnegative : 0 ≤ amplitude)
    (receiverNonnegative : 0 ≤ receiver)
    (sourceCenterNonnegative : 0 ≤ sourceCenter) (sourceShapeNonnegative : 0 ≤ sourceShape)
    (selfNonnegative : 0 ≤ selfBudget) (differenceNonnegative : 0 ≤ difference)
    (sourceBound : sourcePart ≤ sourceCenter * center + sourceShape * raw)
    (selfBound : selfBudget ≤ raw) (amplitudeBound : actualReference ≤ amplitude)
    (referenceBound : reference ≤ sourceShape)
    (differenceBound : difference ≤ own * omega * (center + raw) + foreign) :
    sourcePart + receiver * (reference * selfBudget + difference / omega * actualReference) ≤
      (sourceCenter + sourceShape + receiver * (sourceShape + own * amplitude)) * (center + raw) +
        receiver * amplitude * foreign / omega := by
  have normalized : difference / omega ≤ own * (center + raw) + foreign / omega := by
    apply (div_le_div_of_nonneg_right differenceBound omegaPositive.le).trans_eq
    field_simp [omegaPositive.ne']
    ring
  have referencePart : reference * selfBudget ≤ sourceShape * raw :=
    (mul_le_mul_of_nonneg_right referenceBound selfNonnegative).trans
      (mul_le_mul_of_nonneg_left selfBound sourceShapeNonnegative)
  have differencePart : difference / omega * actualReference ≤
      (own * (center + raw) + foreign / omega) * amplitude :=
    (mul_le_mul_of_nonneg_left amplitudeBound (div_nonneg differenceNonnegative omegaPositive.le)).trans
      (mul_le_mul_of_nonneg_right normalized amplitudeNonnegative)
  have combined := add_le_add sourceBound
    (mul_le_mul_of_nonneg_left (add_le_add referencePart differencePart) receiverNonnegative)
  have slackOne := mul_nonneg sourceCenterNonnegative rawNonnegative
  have slackTwo := mul_nonneg sourceShapeNonnegative centerNonnegative
  have slackThree := mul_nonneg receiverNonnegative (mul_nonneg sourceShapeNonnegative centerNonnegative)
  apply combined.trans
  have identity : sourceCenter * center + sourceShape * raw +
      receiver * (sourceShape * raw + (own * (center + raw) + foreign / omega) * amplitude) +
      sourceCenter * raw + sourceShape * center + receiver * (sourceShape * center) =
      (sourceCenter + sourceShape + receiver * (sourceShape + own * amplitude)) * (center + raw) +
        receiver * amplitude * foreign / omega := by ring
  rw [← identity]
  linarith only [slackOne, slackTwo, slackThree]

theorem exists_uniform_actual_centroid_budget_local_foreign_return :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 →
    ∀ sourceConstant : ℝ, 0 ≤ sourceConstant → ∀ receiverConstant : ℝ, 0 ≤ receiverConstant →
    ∃ constant ≥ (0 : ℝ),
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop), ∀ receiver : Fin count × Fin 4,
    ∀ {sourceRadius : ℝ},
    ∀ shapes : ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
    let changed : Scales := {scales with frequency := frequency}
    let comparison := prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes
    let radius := factor / 39321600 * changed.length (receiver.1.val + 1)
    let foreign := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.firstReceiver radius (power + 1) time -
        comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels receiver.1)
          comparison.secondReceiver radius (power + 1) time‖
    Summable foreign ∧
    actualCentroidComparisonBudget changed comparison receiver factor sourceConstant receiverConstant ≤
      constant * (prepared.rawSourceCenteredState time receiver.1 +
        ∑ patch : Fin 4, prepared.rawSourceShapeBudget time receiver.1 patch) +
      (constant / changed.omega (receiver.1.val + 1)) * (∑' power : ℕ, foreign power) := by
  obtain ⟨ownRadius, ownRadiusPositive, ownCap, ownCapPositive, ownFactory⟩ :=
    exists_uniform_actual_own_local_virtual_return
  obtain ⟨patchRadius, patchRadiusPositive, patchCap, patchCapPositive, patchBase, patchBaseNonnegative, patches⟩ :=
    exists_uniform_actual_patch_macro_virtual_coefficient_series_action
  refine ⟨min ownCap patchCap, lt_min ownCapPositive patchCapPositive, ?_⟩
  intro factor factorPositive factorOne sourceConstant sourceNonnegative receiverConstant receiverNonnegative
  obtain ⟨ownConstant, ownNonnegative, owns⟩ := ownFactory factorPositive factorOne
  let amplitude : ℝ := ‖diskPhysicalTransverseProjection‖ * ownRadius
  let receiver : ℝ := receiverConstant / (factor / 39321600)
  let sourceCenter : ℝ := 144 * (factor / 800)⁻¹ ^ 4
  let sourceShape : ℝ := 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 +
    96 / Real.pi * ((80000 * Real.pi + 2304) / (factor / 8) ^ 2) + 1
  let localConstant := sourceCenter + sourceShape + receiver * (sourceShape + ownConstant * amplitude)
  let foreignCoefficient := receiver * amplitude
  let constant := localConstant + foreignCoefficient
  have amplitudeNonnegative : 0 ≤ amplitude := by dsimp only [amplitude]; positivity
  have receiverNonnegative' : 0 ≤ receiver := by dsimp only [receiver]; positivity
  have sourceCenterNonnegative : 0 ≤ sourceCenter := by dsimp only [sourceCenter]; positivity
  have sourceShapeNonnegative : 0 ≤ sourceShape := by dsimp only [sourceShape]; positivity
  have localNonnegative : 0 ≤ localConstant := by dsimp only [localConstant]; positivity
  have foreignNonnegative : 0 ≤ foreignCoefficient := by dsimp only [foreignCoefficient]; positivity
  refine ⟨constant, add_nonneg localNonnegative foreignNonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [patches scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    owns scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency patchEstimate ownEstimate frequencyOne radii lengths strainSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiving sourceRadius shapes
  rcases receiving with ⟨index, patch⟩
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let centerState := prepared.rawSourceCenteredState time index
  let raw := fun patch : Fin 4 =>
    let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
    let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
        ‖diskNeutralCLM initial - diskNeutralCLM final‖
  let rawDifference := ∑ patch : Fin 4, raw patch
  let original := prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) shapes
  let virtualRadius := factor / 39321600 * length
  let foreignTerm := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
    ‖original.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        original.firstReceiver virtualRadius (power + 1) time -
      original.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        original.secondReceiver virtualRadius (power + 1) time‖
  let foreignSeries := ∑' power : ℕ, foreignTerm power
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have lengthPositive : 0 < length := changed.length_pos _
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonSmall : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos lengthPositive)).mpr
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le
      (by simpa only [one_mul] using (radii (index.val + 1)).le) 2
  have centerNonnegative : 0 ≤ centerState := by
    dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState]
    positivity
  have rawNonnegative (patch : Fin 4) : 0 ≤ raw patch := by dsimp only [raw]; positivity
  have rawSumNonnegative : 0 ≤ rawDifference := Finset.sum_nonneg (fun patch _ => rawNonnegative patch)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have seriesNonnegative : 0 ≤ foreignSeries := by
    apply tsum_nonneg
    intro power
    dsimp only [foreignTerm]
    positivity
  let ownPrepared := prepared.enlargeCap (min_le_left ownCap patchCap)
  let patchPrepared := prepared.enlargeCap (min_le_right ownCap patchCap)
  have actualReturn : Summable foreignTerm ∧
      actualCentroidComparisonBudget changed
        (prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) shapes)
        (index, patch) factor sourceConstant receiverConstant ≤
      localConstant * (centerState + rawDifference) + receiver * amplitude * foreignSeries / omega := by
    obtain ⟨ownShapes, ownActual⟩ := ownEstimate count orbit sectionTime phase dipoleAngle ownPrepared path inside (index, patch)
    obtain ⟨patchShapes, patchActual⟩ := patchEstimate count phase dipoleAngle patchPrepared path inside (index, patch)
    let original := prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) shapes
    let virtualRadius := factor / 39321600 * length
    have virtualNonnegative : 0 ≤ virtualRadius := by dsimp only [virtualRadius]; positivity
    let comparison : MovingPatchFamilySourceComparison (count * 4) :=
      {original with receiverRadius := virtualRadius, receiverRadius_nonnegative := virtualNonnegative}
    have virtualSmall : virtualRadius ≤ (1 / (100000 * 96)) * scales.location (index.val + 1) := by
      change virtualRadius ≤ (1 / (100000 * 96)) * changed.location (index.val + 1)
      have lengthSmall := (lengths (index.val + 1)).le
      change length ≤ 1 * changed.location (index.val + 1) at lengthSmall
      have positive := changed.location_pos (index.val + 1)
      have factorBound := mul_le_mul_of_nonneg_right factorOne lengthPositive.le
      dsimp only [virtualRadius]
      nlinarith
    have foreignActual := patchActual virtualRadius virtualNonnegative virtualSmall
    have ownActual' := ownActual virtualRadius virtualNonnegative le_rfl
    dsimp only at foreignActual ownActual'
    have ownSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole index).first.exteriorTaylorCoefficient (Finset.univ.erase patch)
            comparison.firstReceiver virtualRadius (power + 1) time -
          (comparison.quadrupole index).second.exteriorTaylorCoefficient (Finset.univ.erase patch)
            comparison.secondReceiver virtualRadius (power + 1) time‖) := ownActual'.1
    have foreignSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.firstReceiver virtualRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.secondReceiver virtualRadius (power + 1) time‖) := foreignActual.2.2.1
    have split := comparison.exteriorTaylorCoefficient_erased_weighted_difference_le_own_foreign
      (index, patch) (by norm_num : (0 : ℝ) ≤ 96) ownSummable foreignSummable
    have rawIdentity (source : Fin 4) : (original.source (finProdFinEquiv (index, source))).spectralDifferenceBudget = raw source := by
      with_reducible_and_instances
        dsimp only [original, raw, MovingPatchSourceComparison.spectralDifferenceBudget,
          MovingPatchFamilySourceComparison.source, CascadeSourcePreparedPair.sourceComparison]
    have rawSubset : (∑ source ∈ Finset.univ.erase patch, raw source) ≤ rawDifference :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun source _ _ => rawNonnegative source)
    have ownSeries : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖(comparison.quadrupole index).first.exteriorTaylorCoefficient (Finset.univ.erase patch)
            comparison.firstReceiver virtualRadius (power + 1) time -
          (comparison.quadrupole index).second.exteriorTaylorCoefficient (Finset.univ.erase patch)
            comparison.secondReceiver virtualRadius (power + 1) time‖) ≤ ownConstant * omega * (centerState + rawDifference) := by
      apply ownActual'.2.trans
      have centerIdentity : (‖(fun source => patchCentroid ownPrepared.referenceWitness.trajectory.movingFamily.patchMotion time index source -
          quadrupoleCenter ownPrepared.referenceWitness.trajectory.movingFamily.patchMotion time index) -
          (fun source => patchCentroid ownPrepared.trajectory.movingFamily.patchMotion time index source -
            quadrupoleCenter ownPrepared.trajectory.movingFamily.patchMotion time index)‖ / changed.length (index.val + 1)) = centerState := by
        with_reducible_and_instances
          dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState, length,
            ownPrepared, CascadeSourcePreparedPair.enlargeCap]
      rw [centerIdentity]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add_left
      have boundedShape := (mul_le_mul_of_nonneg_left rawSubset epsilonNonnegative).trans
        ((mul_le_mul_of_nonneg_right epsilonSmall rawSumNonnegative).trans_eq (one_mul _))
      with_reducible_and_instances
        dsimp only [epsilon, length, raw, MovingPatchSourceComparison.spectralDifferenceBudget,
          MovingPatchFamilySourceComparison.source, MovingPatchFamilySourceComparison.quadrupole,
          CascadeSourcePreparedPair.sourceComparison, ownPrepared, CascadeSourcePreparedPair.enlargeCap] at boundedShape ⊢
        exact boundedShape
    have fullBound := split.2.trans (add_le_add_right ownSeries foreignSeries)
    have amplitudeBound : ‖diskPhysicalTransverseProjection (original.final (finProdFinEquiv (index, patch)))‖ ≤ amplitude := by
      have small := (ownShapes (finProdFinEquiv (index, patch))).2.small.le
      exact (diskPhysicalTransverseProjection.le_opNorm _).trans (mul_le_mul_of_nonneg_left small (norm_nonneg _))
    have sourceBound : (∑ label ∈ (Finset.univ.erase (finProdFinEquiv (index, patch))).filter
        (fun label => (finProdFinEquiv.symm label).1 = index),
        (24 * (factor / 800)⁻¹ ^ 4 * (‖(original.source label).displacementDifference‖ / length) +
          96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * (original.source label).spectralDifferenceBudget)) ≤
        sourceCenter * centerState + sourceShape * rawDifference := by
      rw [EulerNonuniqueness.General.sum_erase_filter_equiv_prod finProdFinEquiv]
      have individual (source : Fin 4) (member : source ∈ Finset.univ.erase patch) :
          24 * (factor / 800)⁻¹ ^ 4 * (‖(original.source (finProdFinEquiv (index, source))).displacementDifference‖ / length) +
            96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * (original.source (finProdFinEquiv (index, source))).spectralDifferenceBudget ≤
          48 * (factor / 800)⁻¹ ^ 4 * centerState + 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * raw source := by
        rw [rawIdentity]
        apply add_le_add_right
        have displacement := prepared.sourceComparison_own_displacement_le_centered_array path inside shapes (index, patch) source
        have normalized := div_le_div_of_nonneg_right displacement lengthPositive.le
        have centerIdentity : (2 * ‖(fun source => patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time index source -
              quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time index) -
            (fun source => patchCentroid prepared.trajectory.movingFamily.patchMotion time index source -
              quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index)‖) / length = 2 * centerState := by
          with_reducible_and_instances
            dsimp only [centerState, CascadeSourcePreparedPair.rawSourceCenteredState, length]
            ring
        rw [centerIdentity] at normalized
        exact (mul_le_mul_of_nonneg_left normalized (by positivity)).trans_eq (by ring)
      have summed := Finset.sum_le_sum individual
      have cardIdentity : (Finset.univ.erase patch).card = 3 := by simp
      have rightIdentity : (∑ source ∈ Finset.univ.erase patch,
          (48 * (factor / 800)⁻¹ ^ 4 * centerState + 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * raw source)) =
          3 * (48 * (factor / 800)⁻¹ ^ 4 * centerState) +
            96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 * ∑ source ∈ Finset.univ.erase patch, raw source := by
        rw [Finset.sum_add_distrib, Finset.sum_const, cardIdentity, nsmul_eq_mul, ← Finset.mul_sum]
        norm_num
      rw [rightIdentity] at summed
      apply summed.trans
      have subset : (∑ source ∈ Finset.univ.erase patch, raw source) ≤ rawDifference :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun source _ _ => rawNonnegative source)
      have enlarged := mul_le_mul_of_nonneg_left subset
        (show 0 ≤ 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 by positivity)
      have coefficient : 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 ≤ sourceShape := by
        have nonnegative : 0 ≤ 96 / Real.pi * ((80000 * Real.pi + 2304) / (factor / 8) ^ 2) := by positivity
        dsimp only [sourceShape]
        linarith only [nonnegative]
      have enlarged' := enlarged.trans (mul_le_mul_of_nonneg_right coefficient rawSumNonnegative)
      dsimp only [sourceCenter]
      nlinarith only [enlarged']
    have referenceBudgetBound : (96 / Real.pi * ((80000 * Real.pi * omega + 2304 * changed.strain) / (factor / 8) ^ 2)) / omega ≤ sourceShape := by
      have numerator : 80000 * Real.pi * omega + 2304 * changed.strain ≤ (80000 * Real.pi + 2304) * omega := by
        nlinarith only [strainSmall.le, omegaOne]
      have divided := div_le_div_of_nonneg_right numerator (sq_nonneg (factor / 8))
      have scaled := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left divided (by positivity : 0 ≤ 96 / Real.pi)) omegaPositive.le
      have identity : (96 / Real.pi * (((80000 * Real.pi + 2304) * omega) / (factor / 8) ^ 2)) / omega =
          96 / Real.pi * ((80000 * Real.pi + 2304) / (factor / 8) ^ 2) := by
        field_simp [omegaPositive.ne', factorPositive.ne']
        ring
      rw [identity] at scaled
      apply scaled.trans
      have nonnegative : 0 ≤ 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 := by positivity
      dsimp only [sourceShape]
      linarith only [nonnegative]
    have selfBound : (original.source (finProdFinEquiv (index, patch))).spectralDifferenceBudget ≤ rawDifference := by
      rw [rawIdentity]
      exact Finset.single_le_sum (fun source _ => rawNonnegative source) (Finset.mem_univ patch)
    have scalar := centroidBudgetLocalForeignReturn_scalar omegaPositive centerNonnegative rawSumNonnegative amplitudeNonnegative receiverNonnegative'
      sourceCenterNonnegative sourceShapeNonnegative (original.source (finProdFinEquiv (index, patch))).spectralDifferenceBudget_nonnegative
      (tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))) sourceBound selfBound amplitudeBound referenceBudgetBound fullBound
    refine ⟨foreignSummable, ?_⟩
    with_reducible_and_instances
      dsimp only [actualCentroidComparisonBudget, comparison, virtualRadius, length, omega,
        localConstant, receiver] at scalar ⊢
      simpa only [mul_assoc] using scalar
  have localIncrease := mul_le_mul_of_nonneg_right
    (show localConstant ≤ constant from le_add_of_nonneg_right foreignNonnegative)
    (add_nonneg centerNonnegative rawSumNonnegative)
  have foreignIncrease : receiver * amplitude * foreignSeries / omega ≤ constant * foreignSeries / omega :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (show foreignCoefficient ≤ constant from le_add_of_nonneg_left localNonnegative) seriesNonnegative)
      omegaPositive.le
  refine ⟨actualReturn.1, ?_⟩
  have result := actualReturn.2.trans (add_le_add localIncrease foreignIncrease)
  have rawIdentity : rawDifference = ∑ patch : Fin 4, prepared.rawSourceShapeBudget time index patch := by
    with_reducible_and_instances
      dsimp only [rawDifference, raw, CascadeSourcePreparedPair.rawSourceShapeBudget,
        MovingCentroidGaugeTrajectory.spectralCoordinate]
  rw [rawIdentity] at result
  have coefficientIdentity : constant * foreignSeries / omega =
      (constant / changed.omega (index.val + 1)) * (∑' power : ℕ, foreignTerm power) := by
    dsimp only [foreignSeries, omega]
    ring
  rw [coefficientIdentity] at result
  exact result

end EulerNonuniqueness.Paper


