import EulerNonuniqueness.Section5.CascadePrehitDilationReturn
import EulerNonuniqueness.Section5.CascadeActualPatchMacroVirtualCoefficientAction
import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeOwnLocalVirtualSourceReturn
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity
import EulerNonuniqueness.Section6.MovingErasedOwnForeignSeries

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem dilationCentroidBudget_scalar
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

theorem exists_uniform_actual_prehit_dilation_macro_feedback :
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
    ∀ time ∈ Icc 0 finish,
    let changed : Scales := {scales with frequency := frequency}
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
    let centerState := ‖(fun patch => patchCentroid second time index patch - quadrupoleCenter second time index) -
      (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index)‖ / changed.length (index.val + 1)
    let rawDifference := ∑ patch : Fin 4,
      let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
      let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
      ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
        (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
          ‖diskNeutralCLM initial - diskNeutralCLM final‖
    |relativeDilationPhysicalVelocity changed first second index time| ≤
      tolerance * ‖relativeNormalizedFirstMoment changed first second index time‖ +
      (tolerance + 72 * (96 / Real.pi * (2304 * changed.strain)) +
        constant * changed.omega (index.val + 1) * epsilon) * centerState +
      constant * changed.omega (index.val + 1) * epsilon * rawDifference +
      (constant / changed.location (index.val + 1) ^ 4) * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
  obtain ⟨returnRadius, returnRadiusPositive, returnCap, returnCapPositive, sourceConstant, sourceNonnegative,
    receiverConstant, receiverNonnegative, referenceErrorConstant, referenceErrorOne, returns⟩ :=
    exists_uniform_actual_prehit_dilation_return
  obtain ⟨macroRadius, macroRadiusPositive, macroCap, macroCapPositive, macroBase, macroBaseNonnegative, macros⟩ :=
    exists_uniform_actual_macro_coefficient_series_action
  obtain ⟨patchRadius, patchRadiusPositive, patchCap, patchCapPositive, patchBase, patchBaseNonnegative, patches⟩ :=
    exists_uniform_actual_patch_macro_virtual_coefficient_series_action
  obtain ⟨ownRadius, ownRadiusPositive, ownCap, ownCapPositive, ownFactory⟩ :=
    exists_uniform_actual_own_local_virtual_return
  have referenceErrorNonnegative : 0 ≤ referenceErrorConstant := by linarith only [referenceErrorOne]
  refine ⟨min returnCap (min macroCap (min patchCap ownCap)),
    lt_min returnCapPositive (lt_min macroCapPositive (lt_min patchCapPositive ownCapPositive)), ?_⟩
  intro factor factorPositive factorSmall
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  obtain ⟨ownConstant, ownNonnegative, owns⟩ := ownFactory factorPositive factorOne
  let amplitude : ℝ := ‖diskPhysicalTransverseProjection‖ * ownRadius
  let receiver : ℝ := receiverConstant / (factor / 39321600)
  let sourceCenter : ℝ := 144 * (factor / 800)⁻¹ ^ 4
  let sourceShape : ℝ := 96 * sourceConstant / Real.pi * (factor / 800)⁻¹ ^ 3 +
    96 / Real.pi * ((80000 * Real.pi + 2304) / (factor / 8) ^ 2) + 1
  let localConstant := sourceCenter + sourceShape + receiver * (sourceShape + ownConstant * amplitude)
  let macroConstant : ℝ := 1000000000 * (macroBase + 1) * 96
  let patchConstant : ℝ := 1000000000 * (patchBase + 1) * 96
  let constant := 4 * referenceErrorConstant + 48 * localConstant + 36 * macroConstant +
    48 * receiver * amplitude * patchConstant
  have amplitudeNonnegative : 0 ≤ amplitude := by dsimp only [amplitude]; positivity
  have receiverNonnegative' : 0 ≤ receiver := by dsimp only [receiver]; positivity
  have sourceCenterNonnegative : 0 ≤ sourceCenter := by dsimp only [sourceCenter]; positivity
  have sourceShapeNonnegative : 0 ≤ sourceShape := by dsimp only [sourceShape]; positivity
  have localNonnegative : 0 ≤ localConstant := by dsimp only [localConstant]; positivity
  have macroNonnegative : 0 ≤ macroConstant := by dsimp only [macroConstant]; positivity
  have patchNonnegative : 0 ≤ patchConstant := by dsimp only [patchConstant]; positivity
  refine ⟨constant, by dsimp only [constant]; positivity, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime scaleRoot boundaryConstant threshold referenceConstant
    tolerance rootOne boundaryOne thresholdSmall referenceNonnegative tolerancePositive
  filter_upwards [returns scales amplitudePositive ratioBound alphaPositive orbit sectionTime rootOne boundaryOne thresholdSmall
      referenceNonnegative factorPositive factorSmall tolerancePositive,
    macros scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    patches scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    owns scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative,
    eventually_ge_atTop (1 : ℝ),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1),
    (scales.strain_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency returnEstimate macroEstimate patchEstimate ownEstimate frequencyOne radii lengths strainSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let length := changed.length (index.val + 1)
  let omega := changed.omega (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / length ^ 2
  let centerState := ‖(fun patch => patchCentroid second time index patch - quadrupoleCenter second time index) -
    (fun patch => patchCentroid first time index patch - quadrupoleCenter first time index)‖ / length
  let raw := fun patch : Fin 4 =>
    let initial := diskPhysicalSpectralCoordinate ((prepared.referenceWitness.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
    let final := diskPhysicalSpectralCoordinate ((prepared.trajectory.curve time).2.2 (finProdFinEquiv (index, patch)))
    ‖diskPhysicalTransverseProjection initial - diskPhysicalTransverseProjection final‖ +
      (‖diskPhysicalTransverseProjection initial‖ + ‖diskPhysicalTransverseProjection final‖) *
        ‖diskNeutralCLM initial - diskNeutralCLM final‖
  let rawDifference := ∑ patch : Fin 4, raw patch
  let row := (216360000 * changed.hessian + 576 * changed.strain) *
    ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ /
      changed.location (index.val + 1) ^ 4
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have omegaOne : 1 ≤ omega := frequencyOne.trans (changed.omega_ge_frequency frequencyPositive (by change 1 ≤ scales.ratio; linarith) _)
  have omegaPositive : 0 < omega := zero_lt_one.trans_le omegaOne
  have lengthPositive : 0 < length := changed.length_pos _
  have epsilonNonnegative : 0 ≤ epsilon := by dsimp only [epsilon]; positivity
  have epsilonSmall : epsilon ≤ 1 := by
    apply (div_le_one (sq_pos_of_pos lengthPositive)).mpr
    exact pow_le_pow_left₀ (changed.radius_pos amplitudePositive frequencyPositive ratioPositive _).le (by simpa only [one_mul] using (radii (index.val + 1)).le) 2
  have centerNonnegative : 0 ≤ centerState := by dsimp only [centerState]; positivity
  have rawNonnegative (patch : Fin 4) : 0 ≤ raw patch := by dsimp only [raw]; positivity
  have rawSumNonnegative : 0 ≤ rawDifference := Finset.sum_nonneg (fun patch _ => rawNonnegative patch)
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le 3))
  have rowNonnegative : 0 ≤ row := by dsimp only [row]; positivity
  let returnPrepared := prepared.enlargeCap (min_le_left returnCap (min macroCap (min patchCap ownCap)))
  let macroPrepared := prepared.enlargeCap ((min_le_right returnCap (min macroCap (min patchCap ownCap))).trans (min_le_left macroCap (min patchCap ownCap)))
  let patchPrepared := prepared.enlargeCap (((min_le_right returnCap (min macroCap (min patchCap ownCap))).trans
    (min_le_right macroCap (min patchCap ownCap))).trans (min_le_left patchCap ownCap))
  let ownPrepared := prepared.enlargeCap (((min_le_right returnCap (min macroCap (min patchCap ownCap))).trans
    (min_le_right macroCap (min patchCap ownCap))).trans (min_le_right patchCap ownCap))
  obtain ⟨returnShapes, returned⟩ := returnEstimate count phase dipoleAngle returnPrepared path index nonterminal finish
    finishNonnegative finishBound radialSmall time inside
  obtain ⟨macroShapes, macroSummable, macroBound, macroSelected⟩ :=
    macroEstimate count phase dipoleAngle macroPrepared path fullInside index
  have macroStateIdentity (source : Fin count) : macroPrepared.macroSourceState time source = prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, macroPrepared, CascadeSourcePreparedPair.enlargeCap]
  have macroArrayIdentity : (fun source : Fin count => changed.location (source.val + 1) ^ 4 * macroPrepared.macroSourceState time source) =
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
    funext source
    rw [macroStateIdentity]
  dsimp only at macroBound macroSummable returned
  rw [macroArrayIdentity] at macroBound
  have macroSeries : (∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time
      (factor / 39321600 * changed.location (index.val + 1)) power -
      quadrupoleExteriorCoefficient changed second index time
      (factor / 39321600 * changed.location (index.val + 1)) power‖) ≤ macroConstant * row := by
    let sequence := fun power : ℕ => ‖quadrupoleExteriorCoefficient changed second index time
      (factor / 39321600 * changed.location (index.val + 1)) power -
      quadrupoleExteriorCoefficient changed first index time
      (factor / 39321600 * changed.location (index.val + 1)) power‖
    have pointwise (power : ℕ) : sequence power ≤ (96 : ℝ) ^ (power + 1) * sequence power :=
      le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 96))
    have summable : Summable sequence := Summable.of_nonneg_of_le (fun power => norm_nonneg _) pointwise (by
      simpa only [sequence, second, prepared.referenceIdentity] using macroSummable)
    have estimate := summable.tsum_le_tsum pointwise (by
      simpa only [sequence, second, prepared.referenceIdentity] using macroSummable)
    have weighted : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) * sequence power) ≤ macroConstant * row := by
      calc
        _ ≤ (macroConstant * (216360000 * changed.hessian + 576 * changed.strain) *
            ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖) /
            changed.location (index.val + 1) ^ 4 := (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by
          simpa only [sequence, second, prepared.referenceIdentity, macroConstant, mul_comm] using macroBound)
        _ = _ := by dsimp only [row]; ring
    calc
      _ = ∑' power : ℕ, sequence power := tsum_congr (fun power => norm_sub_rev _ _)
      _ ≤ _ := estimate.trans weighted
  have patchBudget (patch : Fin 4) :
      actualCentroidComparisonBudget changed
        (returnPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (returnShapes patch))
        (index, patch) factor sourceConstant receiverConstant ≤
      localConstant * (centerState + rawDifference) + receiver * amplitude * patchConstant * row / omega := by
    obtain ⟨ownShapes, ownActual⟩ := ownEstimate count orbit sectionTime phase dipoleAngle ownPrepared path fullInside (index, patch)
    obtain ⟨patchShapes, patchActual⟩ := patchEstimate count phase dipoleAngle patchPrepared path fullInside (index, patch)
    let original := returnPrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (returnShapes patch)
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
          MovingPatchFamilySourceComparison.source, CascadeSourcePreparedPair.sourceComparison,
          returnPrepared, CascadeSourcePreparedPair.enlargeCap]
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
          dsimp only [centerState, second, first, length, ownPrepared, CascadeSourcePreparedPair.enlargeCap]
          rw [prepared.referenceIdentity]
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
    have patchArrayIdentity : (fun source : Fin count => changed.location (source.val + 1) ^ 4 * patchPrepared.macroSourceState time source) =
        (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
      funext source
      with_reducible_and_instances
        dsimp only [CascadeSourcePreparedPair.macroSourceState, patchPrepared, CascadeSourcePreparedPair.enlargeCap]
    have foreignBound := foreignActual.2.2.2
    rw [patchArrayIdentity] at foreignBound
    have foreignSeries : (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.firstReceiver virtualRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
            comparison.secondReceiver virtualRadius (power + 1) time‖) ≤ patchConstant * row := by
      calc
        _ ≤ (patchConstant * (216360000 * changed.hessian + 576 * changed.strain) *
            ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖) /
            changed.location (index.val + 1) ^ 4 := (le_div_iff₀ (pow_pos (changed.location_pos _) 4)).mpr (by
          simpa only [patchConstant, mul_comm] using foreignBound)
        _ = _ := by dsimp only [row]; ring
    have fullBound := split.2.trans (add_le_add ownSeries foreignSeries)
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
        have displacement := returnPrepared.sourceComparison_own_displacement_le_centered_array path fullInside (returnShapes patch) (index, patch) source
        have normalized := div_le_div_of_nonneg_right displacement lengthPositive.le
        have centerIdentity : (2 * ‖(fun source => patchCentroid returnPrepared.referenceWitness.trajectory.movingFamily.patchMotion time index source -
              quadrupoleCenter returnPrepared.referenceWitness.trajectory.movingFamily.patchMotion time index) -
            (fun source => patchCentroid returnPrepared.trajectory.movingFamily.patchMotion time index source -
              quadrupoleCenter returnPrepared.trajectory.movingFamily.patchMotion time index)‖) / length = 2 * centerState := by
          with_reducible_and_instances
            dsimp only [centerState, second, first, length, returnPrepared, CascadeSourcePreparedPair.enlargeCap]
            rw [prepared.referenceIdentity]
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
    have scalar := dilationCentroidBudget_scalar omegaPositive centerNonnegative rawSumNonnegative amplitudeNonnegative receiverNonnegative'
      sourceCenterNonnegative sourceShapeNonnegative (original.source (finProdFinEquiv (index, patch))).spectralDifferenceBudget_nonnegative
      (tsum_nonneg (fun _ => mul_nonneg (by positivity) (norm_nonneg _))) sourceBound selfBound amplitudeBound referenceBudgetBound fullBound
    with_reducible_and_instances
      dsimp only [actualCentroidComparisonBudget, comparison, virtualRadius, length, omega,
        localConstant, receiver] at scalar ⊢
      simpa only [mul_assoc] using scalar
  have budgetSum := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => patchBudget patch)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at budgetSum
  have enlarged := mul_le_mul_of_nonneg_left budgetSum (show 0 ≤ 12 * omega * epsilon by positivity)
  have macroEnlarged := mul_le_mul_of_nonneg_left macroSeries (by norm_num : (0 : ℝ) ≤ 36)
  have centerIdentity : (‖(fun patch => patchCentroid first time index patch - quadrupoleCenter first time index) -
      (fun patch => patchCentroid second time index patch - quadrupoleCenter second time index)‖ / length) = centerState := by
    exact congrArg (fun value : ℝ => value / length) (norm_sub_rev _ _)
  with_reducible_and_instances
    dsimp only [returnPrepared, CascadeSourcePreparedPair.enlargeCap] at returned
    dsimp only [first, second, length] at centerIdentity
    rw [centerIdentity] at returned
  have bounded := returned.trans (add_le_add (add_le_add_left macroEnlarged _) enlarged)
  have sourceSlack : 0 ≤ (constant - (36 * macroConstant + 48 * receiver * amplitude * patchConstant)) * row := by
    have identity : constant - (36 * macroConstant + 48 * receiver * amplitude * patchConstant) =
        4 * referenceErrorConstant + 48 * localConstant := by dsimp only [constant]; ring
    rw [identity]
    positivity
  have centerSlack : 0 ≤ (constant - (4 * referenceErrorConstant + 48 * localConstant)) * omega * epsilon * centerState := by
    have identity : constant - (4 * referenceErrorConstant + 48 * localConstant) =
        36 * macroConstant + 48 * receiver * amplitude * patchConstant := by dsimp only [constant]; ring
    rw [identity]
    positivity
  have rawSlack : 0 ≤ (constant - 48 * localConstant) * omega * epsilon * rawDifference := by
    have identity : constant - 48 * localConstant = 4 * referenceErrorConstant + 36 * macroConstant +
        48 * receiver * amplitude * patchConstant := by dsimp only [constant]; ring
    rw [identity]
    positivity
  have epsilonFeedback := mul_le_mul_of_nonneg_right epsilonSmall
    (show 0 ≤ 48 * receiver * amplitude * patchConstant * row by positivity)
  have identity : (12 * omega * epsilon) * (4 * (localConstant * (centerState + rawDifference) +
      receiver * amplitude * patchConstant * row / omega)) =
      48 * localConstant * omega * epsilon * centerState + 48 * localConstant * omega * epsilon * rawDifference +
        epsilon * (48 * receiver * amplitude * patchConstant * row) := by
    field_simp [omegaPositive.ne']
    ring
  rw [identity] at bounded
  have finalIdentity : constant * row = (constant / changed.location (index.val + 1) ^ 4) *
      (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
    dsimp only [row]
    ring
  rw [← finalIdentity]
  with_reducible_and_instances
    change _ ≤ tolerance * ‖relativeNormalizedFirstMoment changed first second index time‖ +
      (tolerance + 72 * (96 / Real.pi * (2304 * changed.strain)) + constant * omega * epsilon) * centerState +
      constant * omega * epsilon * rawDifference + constant * row
    change _ ≤ tolerance * ‖relativeNormalizedFirstMoment changed first second index time‖ +
      (tolerance + 72 * (96 / Real.pi * (2304 * changed.strain)) +
        4 * referenceErrorConstant * omega * epsilon) * centerState + 36 * (macroConstant * row) +
      (48 * localConstant * omega * epsilon * centerState + 48 * localConstant * omega * epsilon * rawDifference +
        epsilon * (48 * receiver * amplitude * patchConstant * row)) at bounded
  apply bounded.trans
  apply sub_nonneg.mp
  convert add_nonneg (add_nonneg (add_nonneg sourceSlack centerSlack) rawSlack)
    (sub_nonneg.mpr (by simpa only [one_mul] using epsilonFeedback)) using 1
  ring

end EulerNonuniqueness.Paper

