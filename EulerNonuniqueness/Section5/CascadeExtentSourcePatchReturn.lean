import EulerNonuniqueness.Section5.CascadeActualQuadrupolePatchFixedMacroSeries
import EulerNonuniqueness.Section5.CascadeActualStrongFirstMoment
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section6.IncomingQuadrupoleSeriesEnvelope

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_source_patch_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 / 8 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ receiver source : Fin count, receiver.val < source.val →
    ∀ receiverPatch : Fin 4, ∀ time ∈ Icc 0 path.stop,
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ patch : Fin 4,
      ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    ∀ radius : ℝ, 0 ≤ radius →
    radius ≤ scales.location (receiver.val + 1) / (100000 * 96) →
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily
    let reference := prepared.referenceWitness.trajectory.movingFamily
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let state := prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed alternative.patchMotion prepared.reference source time‖ +
      ‖quadrupoleCenter alternative.patchMotion time source - quadrupoleCenter reference.patchMotion time source‖ /
        changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let term := fun power : ℕ => (96 : ℝ) ^ (power + 1) *
      ‖(alternative.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid alternative.patchMotion current receiver receiverPatch) radius (power + 1) time -
        (reference.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
          (fun current => patchCentroid reference.patchMotion current receiver receiverPatch) radius (power + 1) time‖
    Summable term ∧ (∑' power : ℕ, term power) ≤
      constant * extent ^ 2 * (changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
        (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state +
          changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
            ‖patchCentroid alternative.patchMotion time receiver receiverPatch - patchCentroid reference.patchMotion time receiver receiverPatch‖) := by
  obtain ⟨sourceRadius, sourcePositive, baseConstant, baseNonnegative, factory⟩ :=
    exists_uniform_actual_foreign_quadrupole_patch_fixed_macro_virtual_series
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, 1000000000000000 * (baseConstant + 1), by positivity, ?_⟩
  intro extent extentOne
  have extentPositive : 0 < extent := zero_lt_one.trans_le extentOne
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have referenceDecay : Tendsto (fun frequency : ℝ => 4 * referenceConstant *
      ({scales with frequency := frequency} : Scales).hessian *
      Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop (𝓝 0) := by
    have exponentialDecay : Tendsto (fun frequency : ℝ =>
        Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop
        (𝓝 (Real.exp (referenceConstant * 0))) :=
      Real.continuous_exp.continuousAt.tendsto.comp
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul referenceConstant)
    simpa using ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (4 * referenceConstant)).mul exponentialDecay
  filter_upwards [factory 96 (by norm_num) scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive (factorSmall.trans (by norm_num)),
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by positivity : (0 : ℝ) < 1 / (300 * extent)),
    referenceDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency estimates alignment radii lengths referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver source ordered receiverPatch time inside
    firstExtent secondExtent radius radiusNonnegative radiusSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let firstCenter := quadrupoleCenter first time source
  let secondCenter := quadrupoleCenter second time source
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let actualLength := changed.length (source.val + 1)
  let length := extent * actualLength
  let shapes := actualShapes prepared path time inside
  let original := (prepared.sourceComparison path inside (finProdFinEquiv (receiver, receiverPatch)) shapes).quadrupole source
  let comparison : MovingPatchFamilySourceComparison 4 :=
    {original with receiverRadius := radius, receiverRadius_nonnegative := radiusNonnegative}
  let centered := prepared.rawSourceCenteredState time source
  let moment := ‖relativeNormalizedFirstMoment changed second prepared.reference source time‖
  let translation := ‖firstCenter - secondCenter‖ / changed.location (source.val + 1)
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let observer := ‖patchCentroid first time receiver receiverPatch - patchCentroid second time receiver receiverPatch‖
  have fullInside : time ∈ Icc 0 path.stop := inside
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 := ⟨by linarith only [inside.1], by linarith only [fullInside.2, path.stopBound]⟩
  have different : receiver ≠ source := fun same => by simp only [same, lt_self_iff_false] at ordered
  have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun same => different (Fin.ext (Nat.add_right_cancel same))
  have gapPositive : 0 < gap := changed.location_distance_pos differentIndices
  have sourcePositive := changed.location_pos (source.val + 1)
  have receiverPositive := changed.location_pos (receiver.val + 1)
  have actualLengthPositive : 0 < actualLength := changed.length_pos _
  have lengthPositive : 0 < length := mul_pos extentPositive actualLengthPositive
  have actualBelow : actualLength ≤ length := le_mul_of_one_le_left actualLengthPositive.le extentOne
  have squareBelow : actualLength ^ 2 ≤ length ^ 2 :=
    pow_le_pow_left₀ actualLengthPositive.le actualBelow 2
  have sourceBelow := changed.location_antitone (show receiver.val + 1 ≤ source.val + 1 by omega)
  have gapIdentity : gap = changed.location (receiver.val + 1) - changed.location (source.val + 1) := abs_of_nonneg (sub_nonneg.mpr sourceBelow)
  have gapReceiver : gap ≤ changed.location (receiver.val + 1) := by rw [gapIdentity]; linarith only [sourcePositive]
  have gapOne : gap ≤ 1 := gapReceiver.trans (changed.location_le_one _)
  have locations := changed.location_sum_le_three_distance differentIndices
  have sourceGap : changed.location (source.val + 1) ≤ 3 * gap := by linarith only [locations, receiverPositive]
  have receiverGap : changed.location (receiver.val + 1) ≤ 3 * gap := by linarith only [locations, sourcePositive]
  have lengthSmall : length ≤ changed.location (source.val + 1) / 300 := by
    have originalSmall : actualLength ≤ (1 / (300 * extent)) * changed.location (source.val + 1) := (lengths (source.val + 1)).le
    have scaled := mul_le_mul_of_nonneg_left originalSmall extentPositive.le
    have identity : extent * ((1 / (300 * extent)) * changed.location (source.val + 1)) =
        changed.location (source.val + 1) / 300 := by
      field_simp [extentPositive.ne']
      ring
    exact scaled.trans_eq identity
  have sourceRadiusSmall : 3 * length ≤ scales.location (source.val + 1) / 100 := by
    change 3 * length ≤ changed.location (source.val + 1) / 100
    linarith only [lengthSmall]
  have lengthGap : length ≤ gap := by linarith only [lengthSmall, sourceGap, gapPositive]
  have physicalSmall : changed.radius (source.val + 1) ≤ length := by
    have originalSmall : changed.radius (source.val + 1) ≤ actualLength := by
      simpa only [one_mul] using (radii (source.val + 1)).le
    exact originalSmall.trans actualBelow
  have firstCenters (patch : Fin 4) : (comparison.first.patch patch).center time = patchCentroid first time source patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have secondCenters (patch : Fin 4) : (comparison.second.patch patch).center time = patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have firstReceiver : comparison.firstReceiver time = patchCentroid first time receiver receiverPatch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver receiverPatch
  have secondReceiver : comparison.secondReceiver time = patchCentroid second time receiver receiverPatch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver receiverPatch
  have sourcePositions (patch : Fin 4) :
      ‖(comparison.first.patch patch).center time - firstCenter‖ ≤ 3 * length ∧
      ‖(comparison.second.patch patch).center time - secondCenter‖ ≤ 3 * length := by
    rw [firstCenters, secondCenters]
    have enlarged : extent * ({scales with frequency := frequency} : Scales).length (source.val + 1) ≤ 3 * length := by
      change length ≤ 3 * length
      linarith only [lengthPositive]
    exact ⟨(firstExtent patch).trans enlarged, (secondExtent patch).trans enlarged⟩
  have seriesActual := estimates count phase dipoleAngle prepared path fullInside shapes (receiver, receiverPatch) source different
    (3 * length) (by positivity) sourceRadiusSmall
    (fun patch => by simpa only [firstCenters, firstCenter, first] using (sourcePositions patch).1)
    (fun patch => by simpa only [secondCenters, secondCenter, second] using (sourcePositions patch).2)
    radius radiusNonnegative (by simpa only [div_eq_mul_inv, one_mul, mul_comm] using radiusSmall)
  have positions : (∑ patch : Fin 4, ‖(comparison.second.patch patch).center time - secondCenter‖) ≤ 12 * length := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => (sourcePositions patch).2)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
    convert summed using 1; ring
  have centeredNonnegative : 0 ≤ centered := div_nonneg (norm_nonneg _) actualLengthPositive.le
  have positionDifference : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center time - firstCenter) -
      ((comparison.second.patch patch).center time - secondCenter)‖) ≤ 4 * length * centered := by
    have actual := prepared.sourceComparison_quadrupole_centered_difference_sum_le path fullInside
      (finProdFinEquiv (receiver, receiverPatch)) shapes source
    have originalBound : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center time - firstCenter) -
        ((comparison.second.patch patch).center time - secondCenter)‖) ≤ 4 * actualLength * centered := by
      apply actual.trans_eq
      dsimp only [centered, CascadeSourcePreparedPair.rawSourceCenteredState, actualLength]
      field_simp [(changed.length_pos _).ne']
      ring
    exact originalBound.trans (by nlinarith only [mul_le_mul_of_nonneg_right actualBelow centeredNonnegative])
  have momentDifference : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter) -
      fourPointSignedMoment (fun patch => (comparison.second.patch patch).center time - secondCenter)‖ ≤
      length ^ 2 / changed.location (source.val + 1) * moment := by
    have identity := prepared.sourceComparison_quadrupole_signed_moment_difference_norm path fullInside
      (finProdFinEquiv (receiver, receiverPatch)) shapes source firstCenter secondCenter
    apply identity.le.trans
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right squareBelow sourcePositive.le) (norm_nonneg _)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have originalReferenceMoment : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter)‖ ≤ actualLength ^ 2 := by
    have signed := prepared.sourceComparison_quadrupole_first_signed_moment path fullInside (finProdFinEquiv (receiver, receiverPatch)) shapes source firstCenter
    change fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter) =
      4 * centroidAsymmetry first time source at signed
    rw [signed, norm_mul]
    norm_num only [Complex.norm_ofNat]
    have coarse := (prepared.referenceWitness.coarse.2.1 time
      (show time ∈ Icc (0 : ℝ) 2 from ⟨inside.1, fullInside.2.trans (path.stopBound.trans (by norm_num))⟩) source).2.2.2.2.1
    have timeOne : time ≤ 1 := fullInside.2.trans path.stopBound
    have exponential : Real.exp (referenceConstant * changed.strain * time) ≤ Real.exp (referenceConstant * changed.strain) :=
      Real.exp_le_exp.mpr (mul_le_of_le_one_right (mul_nonneg referenceNonnegative strainNonnegative) timeOne)
    have timeExponential := mul_le_mul timeOne exponential (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 1)
    have scaled := mul_le_mul_of_nonneg_left timeExponential (show 0 ≤ 4 * referenceConstant * changed.hessian by positivity)
    have normalized : 4 * ‖centroidAsymmetry first time source‖ ≤
        (4 * referenceConstant * changed.hessian * Real.exp (referenceConstant * changed.strain)) * actualLength ^ 2 := by
      have firstBound := mul_le_mul_of_nonneg_left coarse (by norm_num : (0 : ℝ) ≤ 4)
      have secondBound := mul_le_mul_of_nonneg_right scaled (sq_nonneg actualLength)
      exact firstBound.trans (by convert secondBound using 1 <;> dsimp only [first, actualLength] <;> ring)
    exact normalized.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right referenceSmall.le (sq_nonneg actualLength))
  have referenceMoment : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter)‖ ≤ length ^ 2 :=
    originalReferenceMoment.trans squareBelow
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have firstAlignment := (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside
    (receiver, receiverPatch) source different).1
  have secondAlignment := (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside
    (receiver, receiverPatch) source different).2.1
  have combined : ‖(comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)‖ ≤ gap := by
    have identity : (comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter) =
        ((patchCentroid first time receiver receiverPatch - firstCenter) - ideal) -
          ((patchCentroid second time receiver receiverPatch - secondCenter) - ideal) := by rw [firstReceiver, secondReceiver]; abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith only [firstAlignment, secondAlignment, gapPositive])
  have translationIdentity : changed.location (source.val + 1) * translation = ‖firstCenter - secondCenter‖ :=
    mul_div_cancel₀ _ sourcePositive.ne'
  have combinedSplit : ‖(comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)‖ ≤
      observer + changed.location (source.val + 1) * translation := by
    rw [translationIdentity]
    have identity : (comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter) =
        (patchCentroid first time receiver receiverPatch - patchCentroid second time receiver receiverPatch) - (firstCenter - secondCenter) := by
      rw [firstReceiver, secondReceiver]; abel
    rw [identity]
    exact norm_sub_le _ _
  have separated (patch : Fin 4) : gap / 8 ≤
      ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center time‖ := by
    have normIdeal : ‖ideal‖ = gap := by dsimp only [ideal, gap]; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have firstTriangle := norm_sub_norm_le ideal (patchCentroid second time receiver receiverPatch - secondCenter)
    rw [normIdeal, norm_sub_rev ideal] at firstTriangle
    have secondTriangle := norm_sub_norm_le (patchCentroid second time receiver receiverPatch - secondCenter)
      ((comparison.second.patch patch).center time - secondCenter)
    rw [sub_sub_sub_cancel_right] at secondTriangle
    change gap / 8 ≤ ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖
    rw [secondReceiver]
    linarith only [firstTriangle, secondTriangle, secondAlignment, (sourcePositions patch).2, lengthSmall, sourceGap, gapPositive]
  have rawNonnegative : 0 ≤ raw := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have spectralIdentity (patch : Fin 4) : (comparison.source patch).spectralDifferenceBudget = prepared.rawSourceShapeBudget time source patch := by
    with_reducible_and_instances
      dsimp only [comparison, original, MovingPatchFamilySourceComparison.quadrupole,
        FiniteMovingPatchFamily.quadrupoleSubfamily, MovingPatchFamilySourceComparison.source,
        MovingPatchSourceComparison.spectralDifferenceBudget, CascadeSourcePreparedPair.sourceComparison,
        CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate]
  have spectral (patch : Fin 4) : (comparison.source patch).spectralDifferenceBudget ≤ raw := by
    rw [spectralIdentity]
    exact Finset.single_le_sum (fun other _ => by dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity) (Finset.mem_univ patch)
  have displacements (patch : Fin 4) : ‖(comparison.source patch).displacementDifference‖ ≤
      observer + changed.location (source.val + 1) * translation + 4 * length * centered := by
    have component := (Finset.single_le_sum (fun other (_ : other ∈ (Finset.univ : Finset (Fin 4))) =>
      norm_nonneg (((comparison.first.patch other).center time - firstCenter) - ((comparison.second.patch other).center time - secondCenter)))
      (Finset.mem_univ patch)).trans positionDifference
    have identity : (comparison.source patch).displacementDifference =
        ((comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)) -
          (((comparison.first.patch patch).center time - firstCenter) - ((comparison.second.patch patch).center time - secondCenter)) := by
      change (comparison.firstReceiver time - (comparison.first.patch patch).center time) -
        (comparison.secondReceiver time - (comparison.second.patch patch).center time) = _
      abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith only [combinedSplit, component])
  have ratioSmall : 8 * 96 * comparison.receiverRadius / (gap / 8) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < gap / 8)).mpr
    have radiusBound : radius ≤ changed.location (receiver.val + 1) / (100000 * 96) := radiusSmall
    change 8 * 96 * radius ≤ _
    linarith only [radiusBound, receiverGap, gapPositive]
  have bound := MovingPatchFamilySourceComparison.incoming_quadrupole_series_envelope_le comparison firstCenter secondCenter
    (changed.circulation_pos frequencyPositive ratioPositive _).le baseNonnegative gapPositive sourcePositive lengthPositive
    gapOne (changed.location_le_one _) gapReceiver sourceGap lengthGap centeredNonnegative (norm_nonneg _)
    (div_nonneg (norm_nonneg _) sourcePositive.le) rawNonnegative (norm_nonneg _) ratioSmall momentDifference referenceMoment
    positionDifference positions combined combinedSplit
    (fun patch => prepared.sourceComparison_quadrupole_mass_budget path fullInside (finProdFinEquiv (receiver, receiverPatch)) shapes
      amplitudePositive frequencyPositive ratioPositive source patch)
    (fun patch => by
      have identity : (comparison.source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]; exact physicalSmall)
    separated displacements spectral
  dsimp only at seriesActual
  have finalBound := seriesActual.2.trans bound
  have factorization :
      1000000000000000 * (baseConstant + 1) *
        (changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) *
            (centered + moment + translation + raw) +
          changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 * observer) =
      1000000000000000 * (baseConstant + 1) * extent ^ 2 *
        (changed.circulation (source.val + 1) * actualLength ^ 2 / gap ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) *
            (centered + moment + translation + raw) +
          changed.circulation (source.val + 1) * actualLength ^ 2 / gap ^ 5 * observer) := by
    dsimp only [length]
    ring
  rw [factorization] at finalBound
  have termIdentity (power : ℕ) :
      (96 : ℝ) ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖ =
      (96 : ℝ) ^ (power + 1) *
        ‖(prepared.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid second current receiver receiverPatch) radius (power + 1) time -
          (prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source).exteriorTaylorCoefficient Finset.univ
            (fun current => patchCentroid first current receiver receiverPatch) radius (power + 1) time‖ := by
    have firstFamily : comparison.first = prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source := rfl
    have secondFamily : comparison.second = prepared.trajectory.movingFamily.quadrupoleSubfamily source := rfl
    rw [firstFamily, secondFamily]
    dsimp only [FiniteMovingPatchFamily.exteriorTaylorCoefficient]
    rw [firstReceiver, secondReceiver, norm_sub_rev]
  have seriesSummable := seriesActual.1
  change Summable (fun power : ℕ => (96 : ℝ) ^ (power + 1) *
    ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
      comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖) at seriesSummable
  change (∑' power : ℕ, (96 : ℝ) ^ (power + 1) *
    ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver radius (power + 1) time -
      comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver radius (power + 1) time‖) ≤ _ at finalBound
  simp only [termIdentity] at seriesSummable finalBound
  constructor
  · exact seriesSummable
  · simpa only [actualLength, translation, observer, raw, centered, moment, first, second, firstCenter, secondCenter, changed,
      norm_sub_rev] using finalBound

end EulerNonuniqueness.Paper


