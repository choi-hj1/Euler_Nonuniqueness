import EulerNonuniqueness.Section5.CascadePrehitNeutralInputRate
import EulerNonuniqueness.Section5.CascadeActualNeutralReceiverReturn
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

private theorem extent_firstMoment_strong_normalization
    {count : ℕ} (scales : Scales) (first second : PatchMotion count) (index : Fin count) (time : ℝ)
    {radius extentFactor : ℝ} (radiusPositive : 0 < radius) :
    (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
      quadrupoleNeutralSeriesEnvelope scales first second index time radius
        (extentFactor * scales.length (index.val + 1) / radius) =
      ‖quadrupoleExteriorCoefficient scales first index time radius 0‖ *
        ‖relativeNormalizedFirstMoment scales first second index time‖ +
      ‖quadrupoleExteriorCoefficient scales first index time radius 0 - quadrupoleExteriorCoefficient scales second index time radius 0‖ *
        (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 * ‖centroidAsymmetry second time index‖) +
      (8 * extentFactor * scales.location (index.val + 1) / radius) *
        (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1)‖) *
        ‖quadrupoleNormalizedCentroidOffsets first index time (scales.length (index.val + 1)) -
          quadrupoleNormalizedCentroidOffsets second index time (scales.length (index.val + 1))‖ +
      (4 * extentFactor ^ 2 * scales.location (index.val + 1) / radius) *
        (∑' power : ℕ, ‖quadrupoleExteriorCoefficient scales first index time radius (power + 1) -
          quadrupoleExteriorCoefficient scales second index time radius (power + 1)‖) +
      (4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2) *
        ‖quadrupoleExternalReceiverAverage scales first index time - quadrupoleExternalReceiverAverage scales second index time‖ := by
  have lengthPositive := scales.length_pos (index.val + 1)
  have weightPositive : 0 < 4 * scales.location (index.val + 1) / scales.length (index.val + 1) ^ 2 :=
    div_pos (mul_pos (by norm_num) (scales.location_pos _)) (sq_pos_of_pos lengthPositive)
  rw [quadrupoleNeutralSeriesEnvelope,
    quadrupoleNormalizedCentroidOffsets_relative_norm_scale first second index time radiusPositive lengthPositive,
    relativeNormalizedFirstMoment, norm_smul, Real.norm_eq_abs, abs_of_pos weightPositive]
  (field_simp [lengthPositive.ne', radiusPositive.ne']); ring


private theorem extent_firstMoment_input_rate :
    ∃ memory ≥ (1 : ℝ), ∀ extentFactor ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ index : Fin count, ∀ time ∈ Icc 0 path.stop,
      (∀ patch, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
          extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
      (∀ patch, ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
          extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
      let changed : Scales := {scales with frequency := frequency}
      let first := prepared.trajectory.movingFamily.patchMotion
      let second := prepared.reference
      let radius := factor / 39321600 * changed.location (index.val + 1)
      let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖
      ‖relativeFirstMomentExternalVelocity changed first second index time‖ ≤
        (96 / Real.pi * (2304 * changed.strain)) *
          (‖relativeNormalizedFirstMoment changed first second index time‖ +
          (8 * extentFactor * changed.location (index.val + 1) / radius) *
            ‖quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
              quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))‖) +
        (4 * memory * changed.hessian + 4 * extentFactor ^ 2 * changed.location (index.val + 1) / radius) * difference +
        (4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2) *
          ‖quadrupoleExternalReceiverAverage changed first index time - quadrupoleExternalReceiverAverage changed second index time‖ := by
  obtain ⟨memory, memoryOne, neutralHistory⟩ := exists_uniform_paper_reference_neutral_history
  refine ⟨memory, memoryOne, ?_⟩
  intro extentFactor extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor
    boundaryConstant thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_cascade_quadrupole_macro_support amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_length_lt_location ratioBound alphaPositive
      (show (0 : ℝ) < factor / (78643200 * extentFactor) by positivity),
    scales.eventually_cascade_quadrupole_foreign_head_tail amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    neutralHistory scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative]
    with frequency frequencyBound support lengths coefficientBounds referenceBound
  intro count phase dipoleAngle shapeRadius monitor prepared path index time inside firstExtent secondExtent
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily.patchMotion
  let second := prepared.reference
  let radius := factor / 39321600 * changed.location (index.val + 1)
  let weight := 4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2
  let difference := ∑' power : ℕ, ‖quadrupoleExteriorCoefficient changed first index time radius power -
    quadrupoleExteriorCoefficient changed second index time radius power‖
  have fullInside : time ∈ Icc 0 path.stop := inside
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyBound
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith
  have locationPositive := changed.location_pos (index.val + 1)
  have lengthPositive := changed.length_pos (index.val + 1)
  have radiusPositive : 0 < radius := by dsimp only [radius]; positivity
  have weightNonnegative : 0 ≤ weight := by dsimp only [weight]; positivity
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg (fun source =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le
      (pow_nonneg (changed.location_pos _).le _))
  have firstCoefficients := coefficientBounds count phase dipoleAngle prepared path time fullInside index 0
  have secondCoefficients := coefficientBounds count phase dipoleAngle prepared path time fullInside index 1
  have differenceSummable : Summable (fun power : ℕ =>
      ‖quadrupoleExteriorCoefficient changed first index time radius power -
        quadrupoleExteriorCoefficient changed second index time radius power‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun _ => norm_sub_le _ _)
      (firstCoefficients.1.add secondCoefficients.1)
  have differenceBounds := Section6.coefficient_norm_head_tail_le_tsum
    (fun power => quadrupoleExteriorCoefficient changed first index time radius power -
      quadrupoleExteriorCoefficient changed second index time radius power) differenceSummable
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have referenceNeutral := (referenceBound _ prepared.referenceWitness.evolution prepared.referenceWitness.initial
    prepared.referenceWitness.coarse time referenceInside index).2
  have weightedReference : weight * ‖centroidAsymmetry second time index‖ ≤ 4 * memory * changed.hessian := by
    have actual : ‖centroidAsymmetry second time index‖ ≤ memory * changed.hessian * changed.length (index.val + 1) ^ 2 := by
      simpa only [second, prepared.referenceIdentity] using referenceNeutral
    calc
      weight * ‖centroidAsymmetry second time index‖ ≤
          weight * (memory * changed.hessian * changed.length (index.val + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left actual weightNonnegative
      _ = (4 * memory * changed.hessian) * changed.location (index.val + 1) := by
        dsimp only [weight]
        (field_simp [lengthPositive.ne']); ring
      _ ≤ 4 * memory * changed.hessian :=
        mul_le_of_le_one_right (by positivity) (changed.location_le_one _)
  let extent := extentFactor * changed.length (index.val + 1) / radius
  have distancePositive : 0 < changed.location (index.val + 1) / 1000 := by positivity
  have radiusSmall : radius < changed.location (index.val + 1) / 1000 := by
    dsimp only [radius]
    nlinarith only [locationPositive, mul_le_mul_of_nonneg_right factorSmall locationPositive.le]
  have extentNonnegative : 0 ≤ extent := by dsimp only [extent]; positivity
  have extentSmall : extent ≤ 1 / 2 := by
    apply (div_le_iff₀ radiusPositive).mpr
    have lengthBound := mul_le_mul_of_nonneg_left (lengths (index.val + 1)).le (zero_le_one.trans extentOne)
    change extentFactor * changed.length (index.val + 1) ≤
      extentFactor * (factor / (78643200 * extentFactor) * changed.location (index.val + 1)) at lengthBound
    have identity : extentFactor * (factor / (78643200 * extentFactor) * changed.location (index.val + 1)) =
        radius / 2 := by dsimp only [radius]; field_simp [(zero_lt_one.trans_le extentOne).ne']; ring
    rw [identity] at lengthBound
    linarith only [lengthBound]
  have extentIdentity : extent * radius = extentFactor * changed.length (index.val + 1) := div_mul_cancel₀ _ radiusPositive.ne'
  have sourceSupport := support count phase dipoleAngle prepared path time inside index
  have referenceEvolution : FinitePatchEvolution changed second path.stop := by
    simpa only [second, prepared.referenceIdentity] using
      prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])
  have pointRate := relative_firstMoment_external_rate_bound path.evolution referenceEvolution inside
    amplitudePositive frequencyPositive ratioPositive index radiusPositive distancePositive distancePositive radiusSmall radiusSmall
    extentNonnegative extentSmall sourceSupport.2 (by simpa only [second, prepared.referenceIdentity] using sourceSupport.1)
    (by intro patch; rw [extentIdentity]; exact firstExtent patch)
    (by intro patch; rw [extentIdentity]; exact secondExtent patch)
  have actual : ‖relativeFirstMomentExternalVelocity changed first second index time‖ ≤
      weight * quadrupoleNeutralSeriesEnvelope changed first second index time radius extent := by
    rw [relativeFirstMomentExternalVelocity, norm_smul, Real.norm_eq_abs, abs_of_nonneg weightNonnegative]
    exact pointRate
  rw [extent_firstMoment_strong_normalization changed first second index time radiusPositive] at actual
  have firstTerm := mul_le_mul_of_nonneg_right firstCoefficients.2.1
    (norm_nonneg (relativeNormalizedFirstMoment changed first second index time))
  have secondTerm := (mul_le_mul_of_nonneg_left weightedReference
    (norm_nonneg (quadrupoleExteriorCoefficient changed first index time radius 0 -
      quadrupoleExteriorCoefficient changed second index time radius 0))).trans
      (mul_le_mul_of_nonneg_right differenceBounds.1 (by positivity : 0 ≤ 4 * memory * changed.hessian))
  have thirdTerm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left firstCoefficients.2.2
      (show 0 ≤ 8 * extentFactor * changed.location (index.val + 1) / radius by positivity))
    (norm_nonneg (quadrupoleNormalizedCentroidOffsets first index time (changed.length (index.val + 1)) -
      quadrupoleNormalizedCentroidOffsets second index time (changed.length (index.val + 1))))
  have fourthTerm := mul_le_mul_of_nonneg_left differenceBounds.2
    (show 0 ≤ 4 * extentFactor ^ 2 * changed.location (index.val + 1) / radius by positivity)
  have total := actual.trans (add_le_add_right
    (add_le_add (add_le_add (add_le_add firstTerm secondTerm) thirdTerm) fourthTerm) _)
  (convert total using 1; dsimp only [weight, difference]); ring



private theorem extent_firstMoment_scalar
    {extent strain hessian center difference epsilon moment rate memory scale centerConstant shapeConstant returnConstant amplitude : ℝ}
    (budgets series amplitudes : Fin 4 → ℝ)
    (extentOne : 1 ≤ extent) (strainNonnegative : 0 ≤ strain) (hessianSmall : hessian ≤ 1)
    (centerNonnegative : 0 ≤ center) (differenceNonnegative : 0 ≤ difference) (epsilonNonnegative : 0 ≤ epsilon)
    (memoryNonnegative : 0 ≤ memory) (scalePositive : 0 < scale)
    (centerConstantNonnegative : 0 ≤ centerConstant) (shapeConstantNonnegative : 0 ≤ shapeConstant)
    (returnConstantNonnegative : 0 ≤ returnConstant) (amplitudeNonnegative : 0 ≤ amplitude)
    (budgetNonnegative : ∀ patch, 0 ≤ budgets patch) (seriesNonnegative : ∀ patch, 0 ≤ series patch)
    (amplitudesBound : ∀ patch, amplitudes patch ≤ amplitude)
    (bound : rate ≤ moment + centerConstant * extent * strain * center +
      (4 * memory * hessian + 4 * extent ^ 2 / scale) * difference +
        returnConstant * epsilon * ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) :
    let constant := centerConstant + (4 * memory + 4 / scale) + returnConstant * (shapeConstant + amplitude)
    rate ≤ moment + constant * extent ^ 2 *
      (strain * center + difference + epsilon * (strain * ∑ patch, budgets patch + ∑ patch, series patch)) := by
  let constant := centerConstant + (4 * memory + 4 / scale) + returnConstant * (shapeConstant + amplitude)
  have extentNonnegative : 0 ≤ extent := zero_le_one.trans extentOne
  have squareOne : 1 ≤ extent ^ 2 := one_le_pow₀ extentOne
  have extentSquare : extent ≤ extent ^ 2 := by nlinarith only [extentOne]
  have squareNonnegative : 0 ≤ extent ^ 2 := sq_nonneg _
  have budgetSumNonnegative : 0 ≤ ∑ patch, budgets patch := Finset.sum_nonneg (fun patch _ => budgetNonnegative patch)
  have seriesSumNonnegative : 0 ≤ ∑ patch, series patch := Finset.sum_nonneg (fun patch _ => seriesNonnegative patch)
  have sumBound : (∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch)) ≤
      (shapeConstant + amplitude) * (strain * ∑ patch, budgets patch + ∑ patch, series patch) := by
    have summed := Finset.sum_le_sum (fun patch (_ : patch ∈ (Finset.univ : Finset (Fin 4))) =>
      mul_le_mul_of_nonneg_left (amplitudesBound patch) (seriesNonnegative patch))
    rw [← Finset.sum_mul] at summed
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have slackFirst := mul_nonneg shapeConstantNonnegative seriesSumNonnegative
    have slackSecond := mul_nonneg amplitudeNonnegative (mul_nonneg strainNonnegative budgetSumNonnegative)
    nlinarith only [summed, slackFirst, slackSecond]
  have returnNonnegative : 0 ≤ returnConstant * (shapeConstant + amplitude) := by positivity
  have differenceNonnegativeConstant : 0 ≤ 4 * memory + 4 / scale := by positivity
  have centerBelow : centerConstant ≤ constant := by dsimp only [constant]; linarith only [differenceNonnegativeConstant, returnNonnegative]
  have differenceBelow : 4 * memory + 4 / scale ≤ constant := by dsimp only [constant]; linarith only [centerConstantNonnegative, returnNonnegative]
  have returnBelow : returnConstant * (shapeConstant + amplitude) ≤ constant := by dsimp only [constant]; linarith only [centerConstantNonnegative, differenceNonnegativeConstant]
  have constantNonnegative : 0 ≤ constant := centerConstantNonnegative.trans centerBelow
  have centerCoefficient : centerConstant * extent ≤ constant * extent ^ 2 :=
    mul_le_mul centerBelow extentSquare extentNonnegative constantNonnegative
  have hessianExtent : hessian ≤ extent ^ 2 := hessianSmall.trans squareOne
  have scaledHessian := mul_le_mul_of_nonneg_left hessianExtent (show 0 ≤ 4 * memory by positivity)
  have differenceCoefficient : 4 * memory * hessian + 4 * extent ^ 2 / scale ≤ constant * extent ^ 2 := by
    have scaled := mul_le_mul_of_nonneg_right differenceBelow squareNonnegative
    calc
      4 * memory * hessian + 4 * extent ^ 2 / scale ≤ 4 * memory * extent ^ 2 + 4 * extent ^ 2 / scale :=
        add_le_add_right scaledHessian _
      _ = (4 * memory + 4 / scale) * extent ^ 2 := by ring
      _ ≤ constant * extent ^ 2 := scaled
  have returnCoefficient : returnConstant * (shapeConstant + amplitude) ≤ constant * extent ^ 2 :=
    returnBelow.trans (le_mul_of_one_le_right constantNonnegative squareOne)
  have centerBound := mul_le_mul_of_nonneg_right centerCoefficient (mul_nonneg strainNonnegative centerNonnegative)
  have differenceBound := mul_le_mul_of_nonneg_right differenceCoefficient differenceNonnegative
  have returned := mul_le_mul_of_nonneg_left sumBound (mul_nonneg returnConstantNonnegative epsilonNonnegative)
  have returnedCoefficient := mul_le_mul_of_nonneg_right returnCoefficient
    (mul_nonneg epsilonNonnegative (add_nonneg (mul_nonneg strainNonnegative budgetSumNonnegative) seriesSumNonnegative))
  have returnedBound : returnConstant * epsilon * ∑ patch, (shapeConstant * strain * budgets patch + series patch * amplitudes patch) ≤
      constant * extent ^ 2 * epsilon * (strain * ∑ patch, budgets patch + ∑ patch, series patch) := by
    exact returned.trans ((by convert returnedCoefficient using 1 <;> ring))
  have combined := add_le_add_left (add_le_add (add_le_add centerBound differenceBound) returnedBound) moment
  apply bound.trans
  convert combined using 1 <;> ring

theorem exists_uniform_actual_extent_firstMoment_local_foreign_rate :
    ∃ rawCap > (0 : ℝ), ∀ {factor : ℝ}, 0 < factor → factor ≤ 1 / 8 → ∃ constant ≥ (0 : ℝ),
    ∀ extentFactor ≥ (1 : ℝ), ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ index : Fin count, ∀ time ∈ Icc 0 path.stop,
    (∀ patch, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time index patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time index‖ ≤
        extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
    (∀ patch, ‖patchCentroid prepared.reference time index patch - quadrupoleCenter prepared.reference time index‖ ≤
        extentFactor * ({scales with frequency := frequency} : Scales).length (index.val + 1)) →
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
    HasDerivAt (relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index)
      (relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index time) time ∧
    ‖relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index time‖ ≤
      (96 / Real.pi * (2304 * changed.strain)) *
        ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
      constant * extentFactor ^ 2 * (changed.strain * prepared.rawSourceCenteredState time index + difference +
        epsilon * (changed.strain * ∑ patch, prepared.rawSourceShapeBudget time index patch + ∑ patch, series patch)) := by
  obtain ⟨memory, memoryOne, inputRate⟩ := extent_firstMoment_input_rate
  obtain ⟨sourceRadius, sourcePositive, rawCap, rawPositive, sourceConstant, sourceNonnegative, receiverReturn⟩ :=
    exists_uniform_actual_neutral_receiver_firstMoment_return
  refine ⟨rawCap, rawPositive, ?_⟩
  intro factor factorPositive factorSmall
  let scale := factor / 39321600
  let centerConstant := (96 / Real.pi * 2304) * (8 / scale)
  let shapeConstant := (96 / Real.pi * 2304) / (factor / 8) ^ 2
  let returnConstant := sourceConstant / scale
  let amplitude := ‖diskPhysicalTransverseProjection‖ * sourceRadius
  let constant := centerConstant + (4 * memory + 4 / scale) + returnConstant * (shapeConstant + amplitude)
  have scalePositive : 0 < scale := by dsimp only [scale]; positivity
  have memoryNonnegative : 0 ≤ memory := zero_le_one.trans memoryOne
  refine ⟨constant, by dsimp only [constant, centerConstant, shapeConstant, returnConstant, amplitude]; positivity, ?_⟩
  intro extentFactor extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne
  filter_upwards [inputRate extentFactor extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    receiverReturn scales amplitudePositive ratioBound alphaPositive thresholdSmall referenceNonnegative factorPositive
      (factorSmall.trans (by norm_num)),
    eventually_gt_atTop (0 : ℝ),
    (scales.hessian_tendsto_zero ratioBound alphaPositive).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
    with frequency input receiver frequencyPositive hessianSmall
  intro count phase dipoleAngle shapeRadius monitor prepared path index time inside firstExtent secondExtent
  dsimp only
  obtain ⟨shapes, receiverBound⟩ := receiver count orbit sectionTime phase dipoleAngle prepared path inside index
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.trajectory.movingFamily
  let second := prepared.referenceWitness.trajectory.movingFamily
  let radius := scale * changed.location (index.val + 1)
  let epsilon := changed.radius (index.val + 1) ^ 2 / changed.length (index.val + 1) ^ 2
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  let comparisons := fun patch => prepared.sourceComparison path inside (finProdFinEquiv (index, patch)) (shapes patch)
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
  have sourceBound := input count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path index time inside firstExtent secondExtent
  have received := receiverBound
  change (4 * changed.location (index.val + 1) / changed.length (index.val + 1) ^ 2) *
    ‖quadrupoleExternalReceiverAverage changed second.patchMotion index time -
      quadrupoleExternalReceiverAverage changed first.patchMotion index time‖ ≤ _ at received
  have averageIdentity : ‖quadrupoleExternalReceiverAverage changed first.patchMotion index time -
      quadrupoleExternalReceiverAverage changed prepared.reference index time‖ =
      ‖quadrupoleExternalReceiverAverage changed second.patchMotion index time -
        quadrupoleExternalReceiverAverage changed first.patchMotion index time‖ := by
    rw [prepared.referenceIdentity, norm_sub_rev]
  rw [← averageIdentity] at received
  have total := sourceBound.trans (add_le_add_left received _)
  rw [prepared.referenceIdentity] at total
  have ratio8 : 8 * extentFactor * changed.location (index.val + 1) / radius = 8 * extentFactor / scale := by
    dsimp only [radius]; field_simp [scalePositive.ne', locationPositive.ne']; ring
  have ratio4 : 4 * extentFactor ^ 2 * changed.location (index.val + 1) / radius = 4 * extentFactor ^ 2 / scale := by
    dsimp only [radius]; field_simp [scalePositive.ne', locationPositive.ne']; ring
  rw [ratio8, ratio4] at total
  have scalarBound : ‖relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index time‖ ≤
      (96 / Real.pi * (2304 * changed.strain)) * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
      centerConstant * extentFactor * changed.strain * centerState +
      (4 * memory * changed.hessian + 4 * extentFactor ^ 2 / scale) * difference +
      returnConstant * epsilon * ∑ patch, (shapeConstant * changed.strain * budgets patch + series patch * amplitudes patch) := by
    (convert total using 1;
      dsimp only [comparisons, budgets, series, amplitudes, centerState, difference, epsilon, returnConstant, centerConstant,
        shapeConstant, changed, radius, scale, first, second]); ring_nf
  have result := extent_firstMoment_scalar budgets series amplitudes extentOne strainNonnegative hessianSmall.le
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

  change ‖relativeFirstMomentExternalVelocity changed first.patchMotion second.patchMotion index time‖ ≤
    (96 / Real.pi * (2304 * changed.strain)) * ‖relativeNormalizedFirstMoment changed first.patchMotion second.patchMotion index time‖ +
    constant * extentFactor ^ 2 * (changed.strain * centerState + difference +
      epsilon * (changed.strain * ∑ patch, budgets patch + ∑ patch, series patch)) at result
  rw [centerIdentity] at result
  simp_rw [budgetIdentity, seriesIdentity] at result
  have derivative := path.relativeNormalizedFirstMoment_hasDerivAt amplitudePositive frequencyPositive ratioPositive index inside
  rw [prepared.referenceIdentity] at derivative
  exact ⟨derivative, result⟩

end EulerNonuniqueness.Paper
