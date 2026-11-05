import EulerNonuniqueness.Section5.CascadePrehitFirstMomentSourceDefectReturn
import EulerNonuniqueness.Section5.CascadeActualPatchMacroVirtualCoefficientAction
import EulerNonuniqueness.Section5.CascadeActualMacroCoefficientSeriesAction
import EulerNonuniqueness.Section5.CascadeSourceCapMonotonicity

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem firstMomentMacroFeedback_scalar
    {weight strain hessian centerState state epsilon memory radius defect difference
      centerConstant shapeConstant returnConstant macroConstant patchConstant amplitude : ℝ}
    {budgets series amplitudes : Fin 4 → ℝ}
    (weightNonnegative : 0 ≤ weight) (strainNonnegative : 0 ≤ strain) (hessianNonnegative : 0 ≤ hessian)
    (hessianSmall : hessian ≤ 1) (centerNonnegative : 0 ≤ centerState) (stateNonnegative : 0 ≤ state)
    (epsilonSmall : epsilon ≤ 1) (memoryNonnegative : 0 ≤ memory)
    (radiusPositive : 0 < radius) (centerConstantNonnegative : 0 ≤ centerConstant)
    (shapeConstantNonnegative : 0 ≤ shapeConstant) (returnConstantNonnegative : 0 ≤ returnConstant)
    (macroConstantNonnegative : 0 ≤ macroConstant) (patchConstantNonnegative : 0 ≤ patchConstant)
    (amplitudeNonnegative : 0 ≤ amplitude)
    (budgetsNonnegative : ∀ patch, 0 ≤ budgets patch) (seriesNonnegative : ∀ patch, 0 ≤ series patch)
    (amplitudesNonnegative : ∀ patch, 0 ≤ amplitudes patch) (amplitudesBound : ∀ patch, amplitudes patch ≤ amplitude)
    (weightedBudgets : weight * ∑ patch, budgets patch ≤ state)
    (weightedDifference : weight * difference ≤ macroConstant * (216360000 * hessian + 576 * strain) * state)
    (weightedSeries : ∀ patch, weight * series patch ≤ patchConstant * (216360000 * hessian + 576 * strain) * state)
    (bound : defect ≤ max 0 (centerConstant * strain * centerState +
      (4 * memory * hessian + 36 / radius) * difference + returnConstant * epsilon *
        ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch))) :
    weight * defect ≤
      (centerConstant + (4 * memory + 36 / radius) * macroConstant +
        returnConstant * (shapeConstant + 4 * patchConstant * amplitude)) * strain * weight * centerState +
      (centerConstant + (4 * memory + 36 / radius) * macroConstant +
        returnConstant * (shapeConstant + 4 * patchConstant * amplitude)) *
        (216360000 * hessian + 576 * strain) * state := by
  let rate := 216360000 * hessian + 576 * strain
  have rateNonnegative : 0 ≤ rate := by dsimp only [rate]; positivity
  have strainRate : strain ≤ rate := by dsimp only [rate]; nlinarith
  have coefficientNonnegative : 0 ≤ 4 * memory * hessian + 36 / radius := by positivity
  have coefficientBound : 4 * memory * hessian + 36 / radius ≤ 4 * memory + 36 / radius := by
    nlinarith [mul_le_mul_of_nonneg_left hessianSmall (by positivity : 0 ≤ 4 * memory)]
  have differenceBound : weight * ((4 * memory * hessian + 36 / radius) * difference) ≤
      (4 * memory + 36 / radius) * macroConstant * rate * state := by
    calc
      _ = (4 * memory * hessian + 36 / radius) * (weight * difference) := by ring
      _ ≤ (4 * memory * hessian + 36 / radius) * (macroConstant * rate * state) :=
        mul_le_mul_of_nonneg_left weightedDifference coefficientNonnegative
      _ ≤ _ := by
        have actual := mul_le_mul_of_nonneg_right coefficientBound
          (show 0 ≤ macroConstant * rate * state by positivity)
        simpa only [mul_assoc] using actual
  have shapeBound : weight * (shapeConstant * strain * ∑ patch, budgets patch) ≤ shapeConstant * rate * state := by
    calc
      _ = shapeConstant * strain * (weight * ∑ patch, budgets patch) := by ring
      _ ≤ shapeConstant * strain * state := mul_le_mul_of_nonneg_left weightedBudgets (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left strainRate shapeConstantNonnegative) stateNonnegative
  have patchBound (patch : Fin 4) : weight * (series patch * amplitudes patch) ≤ patchConstant * rate * state * amplitude := by
    calc
      _ = (weight * series patch) * amplitudes patch := by ring
      _ ≤ (patchConstant * rate * state) * amplitudes patch :=
        mul_le_mul_of_nonneg_right (weightedSeries patch) (amplitudesNonnegative patch)
      _ ≤ _ := mul_le_mul_of_nonneg_left (amplitudesBound patch) (by positivity)
  have patchesBound : weight * ∑ patch, series patch * amplitudes patch ≤ 4 * patchConstant * rate * state * amplitude := by
    rw [Finset.mul_sum]
    have actual := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) => patchBound patch)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, mul_assoc] using actual
  have sumBound : weight * (∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      (shapeConstant + 4 * patchConstant * amplitude) * rate * state := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
    nlinarith only [shapeBound, patchesBound]
  have sumNonnegative : 0 ≤ ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch) :=
    Finset.sum_nonneg (fun patch _ => add_nonneg
      (mul_nonneg (mul_nonneg shapeConstantNonnegative strainNonnegative) (budgetsNonnegative patch))
      (mul_nonneg (seriesNonnegative patch) (amplitudesNonnegative patch)))
  have returnedBound : weight * (returnConstant * epsilon *
      ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      returnConstant * (shapeConstant + 4 * patchConstant * amplitude) * rate * state := by
    calc
      _ = returnConstant * epsilon * (weight * ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) := by ring
      _ ≤ returnConstant * (weight * ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) :=
        mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left epsilonSmall returnConstantNonnegative).trans_eq (mul_one _))
          (mul_nonneg weightNonnegative sumNonnegative)
      _ ≤ _ := by
        have actual := mul_le_mul_of_nonneg_left sumBound returnConstantNonnegative
        simpa only [mul_assoc] using actual
  have totalNonnegative : 0 ≤ centerConstant * strain * weight * centerState +
      ((4 * memory + 36 / radius) * macroConstant + returnConstant * (shapeConstant + 4 * patchConstant * amplitude)) * rate * state := by positivity
  have maxBound : weight * max 0 (centerConstant * strain * centerState +
      (4 * memory * hessian + 36 / radius) * difference + returnConstant * epsilon *
        ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      centerConstant * strain * weight * centerState +
        ((4 * memory + 36 / radius) * macroConstant + returnConstant * (shapeConstant + 4 * patchConstant * amplitude)) * rate * state := by
    rw [mul_max_of_nonneg _ _ weightNonnegative, mul_zero]
    apply max_le totalNonnegative
    calc
      _ = weight * (centerConstant * strain * centerState) +
          weight * ((4 * memory * hessian + 36 / radius) * difference) +
          weight * (returnConstant * epsilon *
            ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) := by ring
      _ ≤ weight * (centerConstant * strain * centerState) +
          (4 * memory + 36 / radius) * macroConstant * rate * state +
          returnConstant * (shapeConstant + 4 * patchConstant * amplitude) * rate * state :=
        add_le_add (add_le_add_left differenceBound _) returnedBound
      _ = _ := by ring
  apply ((mul_le_mul_of_nonneg_left bound weightNonnegative).trans maxBound).trans
  have centerSlack : 0 ≤ ((4 * memory + 36 / radius) * macroConstant +
      returnConstant * (shapeConstant + 4 * patchConstant * amplitude)) * strain * weight * centerState := by positivity
  have sourceSlack : 0 ≤ centerConstant * rate * state := by positivity
  dsimp only [rate] at *
  nlinarith only [centerSlack, sourceSlack]

private theorem sourceComparison_ownBudget_le_macroSourceState
    {rawCap sourceRadius : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
    {phase dipoleAngle : ℕ → ℝ} {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ}
    {count : ℕ}
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    {time : ℝ} (inside : time ∈ Icc 0 path.stop)
    (shapes : ∀ _patch : Fin 4, ∀ label,
      ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
      ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label))
    (index : Fin count) :
    (∑ patch : Fin 4,
      ((prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch)).source
        (finProdFinEquiv (index, patch))).spectralDifferenceBudget) ≤ prepared.macroSourceState time index := by
  have positive := scales.location_pos (index.val + 1)
  with_reducible_and_instances
    dsimp only [CascadeSourcePreparedPair.macroSourceState, MovingPatchSourceComparison.spectralDifferenceBudget,
      MovingPatchFamilySourceComparison.source, CascadeSourcePreparedPair.sourceComparison]
    apply le_add_of_nonneg_left
    positivity

theorem exists_uniform_actual_prehit_firstMoment_macro_feedback :
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
    let first := prepared.trajectory.movingFamily.patchMotion
    let second := prepared.reference
    let centerState := ‖quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
      quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))‖
    changed.location (index.val + 1) ^ 4 * relativeFirstMomentSourceDefect changed first second index time ≤
      constant * changed.strain * changed.location (index.val + 1) ^ 4 * centerState +
      constant * (216360000 * changed.hessian + 576 * changed.strain) *
        ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖ := by
  obtain ⟨memory, memoryOne, sourceRadius, sourcePositive, sourceCap, sourceCapPositive,
    sourceConstant, sourceConstantNonnegative, sourceFactory⟩ :=
    exists_uniform_actual_prehit_firstMoment_source_defect_return
  obtain ⟨patchRadius, patchRadiusPositive, patchCap, patchCapPositive, patchBase, patchBaseNonnegative, patchFactory⟩ :=
    exists_uniform_actual_patch_macro_virtual_coefficient_series_action
  obtain ⟨macroRadius, macroRadiusPositive, macroCap, macroCapPositive, macroBase, macroBaseNonnegative, macroFactory⟩ :=
    exists_uniform_actual_macro_coefficient_series_action
  refine ⟨min sourceCap (min macroCap patchCap), lt_min sourceCapPositive (lt_min macroCapPositive patchCapPositive), ?_⟩
  intro factor factorPositive factorSmall
  let centerConstant : ℝ := (96 / Real.pi * 2304) * (24 / (factor / 39321600))
  let shapeConstant : ℝ := (96 / Real.pi * 2304) / (factor / 8) ^ 2
  let returnConstant : ℝ := sourceConstant / (factor / 39321600)
  let macroConstant : ℝ := 1000000000 * (macroBase + 1) * 96
  let patchConstant : ℝ := 1000000000 * (patchBase + 1) * 96
  let amplitude : ℝ := ‖diskPhysicalTransverseProjection‖ * sourceRadius
  refine ⟨centerConstant + (4 * memory + 36 / (factor / 39321600)) * macroConstant +
    returnConstant * (shapeConstant + 4 * patchConstant * amplitude), ?_, ?_⟩
  · dsimp only [centerConstant, shapeConstant, returnConstant, macroConstant, patchConstant, amplitude]
    have memoryNonnegative : 0 ≤ memory := by linarith
    positivity
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  have factorOne : factor ≤ 1 := factorSmall.trans (by norm_num)
  filter_upwards [sourceFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall
      referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    patchFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    macroFactory scales amplitudePositive ratioBound alphaPositive orbit sectionTime thresholdSmall referenceNonnegative
      rootOne boundaryOne factorPositive factorOne,
    eventually_ge_atTop (1 : ℝ),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1)]
    with frequency sourceEstimate patchEstimate macroEstimate frequencyOne hessianSmall radii
  intro count phase dipoleAngle shapeRadius monitor prepared path index nonterminal finish finishNonnegative finishBound radialSmall time inside
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let sourcePrepared := prepared.enlargeCap (min_le_left sourceCap (min macroCap patchCap))
  let macroPrepared := prepared.enlargeCap ((min_le_right sourceCap (min macroCap patchCap)).trans (min_le_left macroCap patchCap))
  let patchPrepared := prepared.enlargeCap ((min_le_right sourceCap (min macroCap patchCap)).trans (min_le_right macroCap patchCap))
  have fullInside : time ∈ Icc 0 path.stop := ⟨inside.1, inside.2.trans finishBound⟩
  obtain ⟨shapes, derivative, history, sourceDefect⟩ := sourceEstimate count phase dipoleAngle sourcePrepared path index
    nonterminal finish finishNonnegative finishBound radialSmall time inside
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let comparisons := fun patch => sourcePrepared.sourceComparison path fullInside (finProdFinEquiv (index, patch)) (shapes patch)
  let budgets := fun patch => ((comparisons patch).source (finProdFinEquiv (index, patch))).spectralDifferenceBudget
  let series := fun patch => ∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖(comparisons patch).first.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (comparisons patch).firstReceiver radius (power + 1) time -
      (comparisons patch).second.exteriorTaylorCoefficient (foreignQuadrupolePatchLabels index)
        (comparisons patch).secondReceiver radius (power + 1) time‖
  let amplitudes := fun patch => ‖diskPhysicalTransverseProjection ((comparisons patch).final (finProdFinEquiv (index, patch)))‖
  let difference := ∑' power : ℕ,
    ‖quadrupoleExteriorCoefficient changed prepared.trajectory.movingFamily.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed prepared.reference index time radius power‖
  let centerState := ‖quadrupoleNormalizedCentroidOffsets prepared.trajectory.movingFamily.patchMotion index time (changed.length (index.val + 1)) -
    quadrupoleNormalizedCentroidOffsets prepared.reference index time (changed.length (index.val + 1))‖
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  let state := ‖fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source‖
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have weightNonnegative : 0 ≤ changed.location (index.val + 1) ^ 4 := by positivity
  have scalePositive : 0 < factor / 39321600 := by positivity
  have radiusPositive : 0 < radius := mul_pos scalePositive locationPositive
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _))
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _))
  have epsilonSmall : epsilon ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos lengthPositive)).mpr
    have radiusSmall := (radii (index.val + 1)).le
    simp only [one_mul] at radiusSmall
    have radiusNonnegative := (changed.radius_pos amplitudePositive frequencyPositive ratioPositive (index.val + 1)).le
    change changed.radius (index.val + 1) ≤ changed.length (index.val + 1) at radiusSmall
    simpa only [one_mul] using (sq_le_sq₀ radiusNonnegative lengthPositive.le).mpr radiusSmall
  have macroStateIdentity (source : Fin count) : macroPrepared.macroSourceState time source = prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, macroPrepared, CascadeSourcePreparedPair.enlargeCap]
  have sourceStateIdentity (source : Fin count) : sourcePrepared.macroSourceState time source = prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, sourcePrepared, CascadeSourcePreparedPair.enlargeCap]
  have patchStateIdentity (source : Fin count) : patchPrepared.macroSourceState time source = prepared.macroSourceState time source := by
    with_reducible_and_instances
      dsimp only [CascadeSourcePreparedPair.macroSourceState, patchPrepared, CascadeSourcePreparedPair.enlargeCap]
  have macroArrayIdentity :
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * macroPrepared.macroSourceState time source) =
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
    funext source
    rw [macroStateIdentity]
  have patchArrayIdentity :
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * patchPrepared.macroSourceState time source) =
      (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) := by
    funext source
    rw [patchStateIdentity]
  have weightedSeries (patch : Fin 4) : changed.location (index.val + 1) ^ 4 * series patch ≤
      patchConstant * (216360000 * changed.hessian + 576 * changed.strain) * state := by
    obtain ⟨patchShapes, patchBounds⟩ := patchEstimate count phase dipoleAngle patchPrepared path fullInside (index, patch)
    have radiusSmall : radius ≤ (1 / (100000 * 96)) * scales.location (index.val + 1) := by
      have scaled := mul_le_mul_of_nonneg_right factorOne locationPositive.le
      simp only [one_mul] at scaled
      change factor * changed.location (index.val + 1) ≤ changed.location (index.val + 1) at scaled
      change factor / 39321600 * changed.location (index.val + 1) ≤ _
      change factor / 39321600 * changed.location (index.val + 1) ≤
        (1 / (100000 * 96)) * changed.location (index.val + 1)
      nlinarith only [scaled, locationPositive]
    have actual := (patchBounds radius radiusPositive.le radiusSmall).2.2.2
    rw [patchArrayIdentity] at actual
    exact actual
  obtain ⟨macroShapes, macroSummable, macroWeighted, macroSelected⟩ :=
    macroEstimate count phase dipoleAngle macroPrepared path fullInside index
  rw [macroArrayIdentity] at macroWeighted
  let macroSequence := fun power : ℕ =>
    ‖quadrupoleExteriorCoefficient changed prepared.referenceWitness.trajectory.movingFamily.patchMotion index time radius power -
      quadrupoleExteriorCoefficient changed prepared.trajectory.movingFamily.patchMotion index time radius power‖
  have actualMacroSummable : Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) * macroSequence power) := macroSummable
  have termBound (power : ℕ) : macroSequence power ≤ (96 : ℝ) ^ (power + 1) * macroSequence power := by
    have powerOne : (1 : ℝ) ≤ 96 ^ (power + 1) := one_le_pow₀ (by norm_num)
    have nonnegative : 0 ≤ macroSequence power := norm_nonneg _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right powerOne nonnegative
  have plainSummable : Summable macroSequence := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) termBound actualMacroSummable
  have differenceIdentity : difference = ∑' power : ℕ, macroSequence power := by
    apply tsum_congr
    intro power
    dsimp only [difference, macroSequence]
    rw [prepared.referenceIdentity, norm_sub_rev]
  have weightedDifference : changed.location (index.val + 1) ^ 4 * difference ≤
      macroConstant * (216360000 * changed.hessian + 576 * changed.strain) * state := by
    rw [differenceIdentity]
    exact (mul_le_mul_of_nonneg_left (plainSummable.tsum_le_tsum termBound actualMacroSummable) weightNonnegative).trans macroWeighted
  have budgetBound : (∑ patch : Fin 4, budgets patch) ≤ prepared.macroSourceState time index := by
    have actual := sourceComparison_ownBudget_le_macroSourceState sourcePrepared path fullInside shapes index
    rw [sourceStateIdentity] at actual
    exact actual
  have evaluatedState : changed.location (index.val + 1) ^ 4 * prepared.macroSourceState time index ≤ state := by
    have actual := norm_le_pi_norm (fun source : Fin count => changed.location (source.val + 1) ^ 4 * prepared.macroSourceState time source) index
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg weightNonnegative (prepared.macroSourceState_nonnegative time index))] at actual
    exact actual
  have weightedBudgets : changed.location (index.val + 1) ^ 4 * ∑ patch : Fin 4, budgets patch ≤ state :=
    (mul_le_mul_of_nonneg_left budgetBound weightNonnegative).trans evaluatedState
  have amplitudesBound (patch : Fin 4) : amplitudes patch ≤ amplitude := by
    have actual := diskPhysicalTransverseProjection.le_opNorm ((comparisons patch).final (finProdFinEquiv (index, patch)))
    apply actual.trans
    exact mul_le_mul_of_nonneg_left (shapes patch (finProdFinEquiv (index, patch))).2.small.le (norm_nonneg _)
  have ratio24 : 24 * changed.location (index.val + 1) / radius = 24 / (factor / 39321600) := by
    dsimp only [radius]
    field_simp [scalePositive.ne', locationPositive.ne']
    ring
  have ratio36 : 36 * changed.location (index.val + 1) / radius = 36 / (factor / 39321600) := by
    dsimp only [radius]
    field_simp [scalePositive.ne', locationPositive.ne']
    ring
  have scalarBound : relativeFirstMomentSourceDefect changed prepared.trajectory.movingFamily.patchMotion prepared.reference index time ≤
      max 0 (centerConstant * changed.strain * centerState +
        (4 * memory * changed.hessian + 36 / (factor / 39321600)) * difference + returnConstant * epsilon *
          ∑ patch : Fin 4, (shapeConstant * changed.strain * budgets patch + series patch * amplitudes patch)) := by
    apply sourceDefect.trans_eq
    congr 1
    with_reducible_and_instances
      dsimp only [comparisons, budgets, series, amplitudes, centerState, difference, epsilon, returnConstant,
        sourcePrepared, CascadeSourcePreparedPair.enlargeCap, CascadeSourcePreparedPair.sourceComparison,
        MovingPatchFamilySourceComparison.source]
    rw [ratio24, ratio36]
    dsimp only [centerConstant, shapeConstant, changed, radius]
    ring
  have result := firstMomentMacroFeedback_scalar weightNonnegative strainNonnegative hessianNonnegative hessianSmall.le
    (norm_nonneg _) (norm_nonneg _) epsilonSmall (show 0 ≤ memory by linarith only [memoryOne]) scalePositive
    (show 0 ≤ centerConstant by dsimp only [centerConstant]; positivity)
    (show 0 ≤ shapeConstant by dsimp only [shapeConstant]; positivity)
    (show 0 ≤ returnConstant by dsimp only [returnConstant]; positivity)
    (show 0 ≤ macroConstant by dsimp only [macroConstant]; positivity)
    (show 0 ≤ patchConstant by dsimp only [patchConstant]; positivity)
    (show 0 ≤ amplitude by dsimp only [amplitude]; positivity)
    (fun patch => ((comparisons patch).source (finProdFinEquiv (index, patch))).spectralDifferenceBudget_nonnegative)
    (fun _ => tsum_nonneg (fun _ => by positivity)) (fun _ => norm_nonneg _) amplitudesBound
    weightedBudgets weightedDifference weightedSeries scalarBound
  exact result

end EulerNonuniqueness.Paper
