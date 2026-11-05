import EulerNonuniqueness.Section5.CascadeActualQuadrupoleVelocity
import EulerNonuniqueness.Section5.CascadeActualStrongFirstMoment
import EulerNonuniqueness.Section5.CascadeMacroFollowerGeometry
import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section6.IncomingQuadrupoleSeriesEnvelope
import EulerNonuniqueness.Section6.MovingQuadrupoleVelocitySeriesEnvelope

noncomputable section

open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_extent_source_velocity_return :
    ∃ rawCap > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
    ∀ extent : ℝ, 1 ≤ extent →
    ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
    ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
    ∀ {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ},
    threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
    0 < factor → factor ≤ 1 →
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
    ∀ time ∈ Icc 0 path.stop, ∀ receiver source : Fin count, receiver.val < source.val →
    (∀ patch, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
      quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    (∀ patch, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
      quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤
        extent * ({scales with frequency := frequency} : Scales).length (source.val + 1)) →
    ∀ receiverPatch : Fin 4,
    let changed : Scales := {scales with frequency := frequency}
    let alternative := prepared.trajectory.movingFamily
    let reference := prepared.referenceWitness.trajectory.movingFamily
    let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
    let length := changed.length (source.val + 1)
    let state := prepared.rawSourceCenteredState time source +
      ‖relativeNormalizedFirstMoment changed alternative.patchMotion prepared.reference source time‖ +
      ‖quadrupoleCenter alternative.patchMotion time source - quadrupoleCenter reference.patchMotion time source‖ /
        changed.location (source.val + 1) + ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
    let sharp := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
      (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) * state +
        changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 *
          ‖patchCentroid alternative.patchMotion time receiver receiverPatch -
            patchCentroid reference.patchMotion time receiver receiverPatch‖
    let velocity := ‖biotSavart ((alternative.quadrupoleSubfamily source).vorticity time)
        (patchCentroid alternative.patchMotion time receiver receiverPatch) -
      biotSavart ((reference.quadrupoleSubfamily source).vorticity time)
        (patchCentroid reference.patchMotion time receiver receiverPatch)‖
    velocity ≤ constant * extent ^ 2 * gap * sharp ∧
      velocity / changed.location (receiver.val + 1) ≤ constant * extent ^ 2 * sharp := by
  obtain ⟨sourceRadius, sourcePositive, baseConstant, baseNonnegative, factory⟩ :=
    exists_uniform_actual_foreign_quadrupole_relative_velocity
  obtain ⟨rawCap, rawPositive, actualShapes⟩ := exists_actual_source_stopped_shape_radius sourcePositive
  refine ⟨rawCap, rawPositive, 1000000000000000 * (baseConstant + 1), by positivity, ?_⟩
  intro extent extentOne scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot factor boundaryConstant
    thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall
  have extentPositive : 0 < extent := zero_lt_one.trans_le extentOne
  have referenceDecay : Tendsto (fun frequency : ℝ => 4 * referenceConstant *
      ({scales with frequency := frequency} : Scales).hessian *
      Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop (𝓝 0) := by
    have exponentialDecay : Tendsto (fun frequency : ℝ =>
        Real.exp (referenceConstant * ({scales with frequency := frequency} : Scales).strain)) atTop
        (𝓝 (Real.exp (referenceConstant * 0))) :=
      Real.continuous_exp.continuousAt.tendsto.comp
        ((scales.strain_tendsto_zero ratioBound alphaPositive).const_mul referenceConstant)
    simpa using ((scales.hessian_tendsto_zero ratioBound alphaPositive).const_mul (4 * referenceConstant)).mul exponentialDecay
  filter_upwards [factory scales amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith only [ratioBound] : 1 ≤ scales.ratio) (by norm_num : (0 : ℝ) < 1),
    scales.eventually_length_lt_location ratioBound alphaPositive (by positivity : 0 < 1 / (300 * extent)),
    referenceDecay.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop (1 : ℝ)]
    with frequency estimates alignment radii lengths referenceSmall frequencyOne
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver source ordered firstExtent secondExtent receiverPatch
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let firstCenter := quadrupoleCenter first time source
  let secondCenter := quadrupoleCenter second time source
  let gap := |changed.location (receiver.val + 1) - changed.location (source.val + 1)|
  let length := changed.length (source.val + 1)
  let enlargedLength := extent * length
  let shapes := actualShapes prepared path time inside
  let comparison := (prepared.sourceComparison path inside (finProdFinEquiv (receiver, receiverPatch)) shapes).quadrupole source
  let virtual : MovingPatchFamilySourceComparison 4 :=
    {comparison with receiverRadius := 0, receiverRadius_nonnegative := le_rfl}
  let centered := prepared.rawSourceCenteredState time source
  let moment := ‖relativeNormalizedFirstMoment changed second prepared.reference source time‖
  let translation := ‖firstCenter - secondCenter‖ / changed.location (source.val + 1)
  let raw := ∑ patch : Fin 4, prepared.rawSourceShapeBudget time source patch
  let observer := ‖patchCentroid first time receiver receiverPatch - patchCentroid second time receiver receiverPatch‖
  have fullInside : time ∈ Icc 0 path.stop := inside
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith only [inside.1], by linarith only [inside.2, path.stopBound]⟩
  have different : receiver ≠ source := fun same => by simp only [same, lt_self_iff_false] at ordered
  have differentIndices : receiver.val + 1 ≠ source.val + 1 := fun same => different (Fin.ext (Nat.add_right_cancel same))
  have gapPositive : 0 < gap := changed.location_distance_pos differentIndices
  have sourcePositive := changed.location_pos (source.val + 1)
  have receiverPositive := changed.location_pos (receiver.val + 1)
  have lengthPositive : 0 < length := changed.length_pos _
  have enlargedPositive : 0 < enlargedLength := mul_pos extentPositive lengthPositive
  have lengthEnlarged : length ≤ enlargedLength := le_mul_of_one_le_left lengthPositive.le extentOne
  have sourceBelow := changed.location_antitone (show receiver.val + 1 ≤ source.val + 1 by omega)
  have gapIdentity : gap = changed.location (receiver.val + 1) - changed.location (source.val + 1) :=
    abs_of_nonneg (sub_nonneg.mpr sourceBelow)
  have gapReceiver : gap ≤ changed.location (receiver.val + 1) := by rw [gapIdentity]; linarith only [sourcePositive]
  have gapOne : gap ≤ 1 := gapReceiver.trans (changed.location_le_one _)
  have locations := changed.location_sum_le_three_distance differentIndices
  have sourceGap : changed.location (source.val + 1) ≤ 3 * gap := by linarith only [locations, receiverPositive]
  have lengthSmall : enlargedLength ≤ changed.location (source.val + 1) / 300 := by
    have actual := (lengths (source.val + 1)).le
    change length ≤ (1 / (300 * extent)) * changed.location (source.val + 1) at actual
    have multiplied := mul_le_mul_of_nonneg_left actual extentPositive.le
    exact multiplied.trans_eq (by field_simp [extentPositive.ne']; ring)
  have sourceRadiusSmall : 3 * enlargedLength ≤ scales.location (source.val + 1) / 100 := by
    change 3 * enlargedLength ≤ changed.location (source.val + 1) / 100
    linarith only [lengthSmall, sourcePositive]
  have enlargedGap : enlargedLength ≤ gap := by linarith only [lengthSmall, sourceGap, gapPositive]
  have physicalSmall : changed.radius (source.val + 1) ≤ enlargedLength := by
    have actual : changed.radius (source.val + 1) ≤ length := by simpa only [one_mul] using (radii (source.val + 1)).le
    exact actual.trans lengthEnlarged
  have firstCenters (patch : Fin 4) : (comparison.first.patch patch).center time = patchCentroid first time source patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have secondCenters (patch : Fin 4) : (comparison.second.patch patch).center time = patchCentroid second time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have firstReceiver : comparison.firstReceiver time = patchCentroid first time receiver receiverPatch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver receiverPatch
  have secondReceiver : comparison.secondReceiver time = patchCentroid second time receiver receiverPatch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver receiverPatch
  have sourcePositions (patch : Fin 4) :
      ‖(comparison.first.patch patch).center time - firstCenter‖ ≤ enlargedLength ∧
      ‖(comparison.second.patch patch).center time - secondCenter‖ ≤ enlargedLength := by
    rw [firstCenters, secondCenters]
    exact ⟨firstExtent patch, secondExtent patch⟩
  have velocityActual := estimates count phase dipoleAngle prepared path fullInside shapes (receiver, receiverPatch) source different
    (3 * enlargedLength) (by positivity) sourceRadiusSmall
    (fun patch => (firstExtent patch).trans (by change enlargedLength ≤ 3 * enlargedLength; linarith only [enlargedPositive]))
    (fun patch => (secondExtent patch).trans (by change enlargedLength ≤ 3 * enlargedLength; linarith only [enlargedPositive]))
  have positions : (∑ patch : Fin 4, ‖(comparison.second.patch patch).center time - secondCenter‖) ≤ 12 * enlargedLength := by
    have summed := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 4))) (fun patch _ => (sourcePositions patch).2)
    norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at summed
    linarith only [summed, enlargedPositive]
  have centeredNonnegative : 0 ≤ centered := div_nonneg (norm_nonneg _) lengthPositive.le
  have positionDifference : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center time - firstCenter) -
      ((comparison.second.patch patch).center time - secondCenter)‖) ≤ 4 * enlargedLength * centered := by
    have actual := prepared.sourceComparison_quadrupole_centered_difference_sum_le path fullInside
      (finProdFinEquiv (receiver, receiverPatch)) shapes source
    have normalized : (∑ patch : Fin 4, ‖((comparison.first.patch patch).center time - firstCenter) -
        ((comparison.second.patch patch).center time - secondCenter)‖) ≤ 4 * length * centered := by
      apply actual.trans_eq
      dsimp only [centered, CascadeSourcePreparedPair.rawSourceCenteredState, length]
      field_simp [(changed.length_pos _).ne']; ring
    exact normalized.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left lengthEnlarged (by norm_num : (0 : ℝ) ≤ 4)) centeredNonnegative)
  have momentDifference : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter) -
      fourPointSignedMoment (fun patch => (comparison.second.patch patch).center time - secondCenter)‖ ≤
      enlargedLength ^ 2 / changed.location (source.val + 1) * moment := by
    have exactMoment := prepared.sourceComparison_quadrupole_signed_moment_difference_norm path fullInside
      (finProdFinEquiv (receiver, receiverPatch)) shapes source firstCenter secondCenter
    change _ = length ^ 2 / changed.location (source.val + 1) * moment at exactMoment
    rw [exactMoment]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ lengthPositive.le lengthEnlarged 2) sourcePositive.le) (norm_nonneg _)
  have frequencyPositive : 0 < changed.frequency := zero_lt_one.trans_le frequencyOne
  have ratioPositive : 0 < changed.ratio := by change 0 < scales.ratio; linarith only [ratioBound]
  have strainNonnegative : 0 ≤ changed.strain := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (sq_nonneg _)
  have hessianNonnegative : 0 ≤ changed.hessian := tsum_nonneg fun index =>
    div_nonneg (changed.circulation_pos frequencyPositive ratioPositive _).le (pow_nonneg (changed.location_pos _).le _)
  have referenceMoment : ‖fourPointSignedMoment (fun patch => (comparison.first.patch patch).center time - firstCenter)‖ ≤ length ^ 2 := by
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
        (4 * referenceConstant * changed.hessian * Real.exp (referenceConstant * changed.strain)) * length ^ 2 := by
      have firstBound := mul_le_mul_of_nonneg_left coarse (by norm_num : (0 : ℝ) ≤ 4)
      have secondBound := mul_le_mul_of_nonneg_right scaled (sq_nonneg length)
      exact firstBound.trans (by convert secondBound using 1 <;> dsimp only [first, length] <;> ring)
    exact normalized.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right referenceSmall.le (sq_nonneg length))
  have enlargedReferenceMoment := referenceMoment.trans (pow_le_pow_left₀ lengthPositive.le lengthEnlarged 2)
  let ideal : ℂ := (changed.location (receiver.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  have firstAlignment := (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside
    (receiver, receiverPatch) source different).1
  have secondAlignment := (alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time fullInside
    (receiver, receiverPatch) source different).2.1
  have combined : ‖(comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)‖ ≤ gap := by
    have identity : (comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter) =
        ((patchCentroid first time receiver receiverPatch - firstCenter) - ideal) -
          ((patchCentroid second time receiver receiverPatch - secondCenter) - ideal) := by
      rw [firstReceiver, secondReceiver]; abel
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
  have normIdeal : ‖ideal‖ = gap := by dsimp only [ideal, gap]; rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have receiverUpper : ‖patchCentroid second time receiver receiverPatch - secondCenter‖ ≤ 19 * gap / 16 := by
    have triangle := norm_add_le ((patchCentroid second time receiver receiverPatch - secondCenter) - ideal) ideal
    rw [sub_add_cancel, normIdeal] at triangle
    linarith only [triangle, secondAlignment]
  have separated (patch : Fin 4) : gap / 8 ≤
      ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center time‖ := by
    have firstTriangle := norm_sub_norm_le ideal (patchCentroid second time receiver receiverPatch - secondCenter)
    rw [normIdeal, norm_sub_rev ideal] at firstTriangle
    have secondTriangle := norm_sub_norm_le (patchCentroid second time receiver receiverPatch - secondCenter)
      ((comparison.second.patch patch).center time - secondCenter)
    rw [sub_sub_sub_cancel_right] at secondTriangle
    change gap / 8 ≤ ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖
    rw [secondReceiver]
    linarith only [firstTriangle, secondTriangle, secondAlignment, (sourcePositions patch).2, lengthSmall, sourceGap, gapPositive]
  have patchDistanceUpper (patch : Fin 4) :
      ‖(comparison.source patch).secondReceiver - (comparison.source patch).second.center time‖ ≤ 16 * (gap / 8) := by
    have triangle := norm_sub_le (patchCentroid second time receiver receiverPatch - secondCenter)
      ((comparison.second.patch patch).center time - secondCenter)
    rw [sub_sub_sub_cancel_right] at triangle
    change ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ ≤ _
    rw [secondReceiver]
    linarith only [triangle, receiverUpper, (sourcePositions patch).2, lengthSmall, sourceGap, gapPositive]
  have rawNonnegative : 0 ≤ raw := by dsimp only [raw, CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity
  have spectralIdentity (patch : Fin 4) : (virtual.source patch).spectralDifferenceBudget = prepared.rawSourceShapeBudget time source patch := by
    with_reducible_and_instances
      dsimp only [virtual, comparison, MovingPatchFamilySourceComparison.quadrupole,
        FiniteMovingPatchFamily.quadrupoleSubfamily, MovingPatchFamilySourceComparison.source,
        MovingPatchSourceComparison.spectralDifferenceBudget, CascadeSourcePreparedPair.sourceComparison,
        CascadeSourcePreparedPair.rawSourceShapeBudget, MovingCentroidGaugeTrajectory.spectralCoordinate]
  have spectral (patch : Fin 4) : (virtual.source patch).spectralDifferenceBudget ≤ raw := by
    rw [spectralIdentity]
    exact Finset.single_le_sum (fun other _ => by dsimp only [CascadeSourcePreparedPair.rawSourceShapeBudget]; positivity) (Finset.mem_univ patch)
  have displacements (patch : Fin 4) : ‖(virtual.source patch).displacementDifference‖ ≤
      observer + changed.location (source.val + 1) * translation + 4 * enlargedLength * centered := by
    have component := (Finset.single_le_sum (fun other (_ : other ∈ (Finset.univ : Finset (Fin 4))) =>
      norm_nonneg (((comparison.first.patch other).center time - firstCenter) - ((comparison.second.patch other).center time - secondCenter)))
      (Finset.mem_univ patch)).trans positionDifference
    have identity : (virtual.source patch).displacementDifference =
        ((comparison.firstReceiver time - firstCenter) - (comparison.secondReceiver time - secondCenter)) -
          (((comparison.first.patch patch).center time - firstCenter) - ((comparison.second.patch patch).center time - secondCenter)) := by
      change (comparison.firstReceiver time - (comparison.first.patch patch).center time) -
        (comparison.secondReceiver time - (comparison.second.patch patch).center time) = _
      abel
    rw [identity]
    exact (norm_sub_le _ _).trans (by linarith only [combinedSplit, component])
  have ratioSmall : 8 * 96 * virtual.receiverRadius / (gap / 8) ≤ 1 / 2 := by
    change 8 * 96 * 0 / (gap / 8) ≤ (1 / 2 : ℝ)
    norm_num
  have envelopeBound := MovingPatchFamilySourceComparison.incoming_quadrupole_series_envelope_le virtual firstCenter secondCenter
    (changed.circulation_pos frequencyPositive ratioPositive _).le baseNonnegative gapPositive sourcePositive enlargedPositive
    gapOne (changed.location_le_one _) gapReceiver sourceGap enlargedGap centeredNonnegative (norm_nonneg _)
    (div_nonneg (norm_nonneg _) sourcePositive.le) rawNonnegative (norm_nonneg _) ratioSmall momentDifference enlargedReferenceMoment
    positionDifference positions combined combinedSplit
    (fun patch => prepared.sourceComparison_quadrupole_mass_budget path fullInside (finProdFinEquiv (receiver, receiverPatch)) shapes
      amplitudePositive frequencyPositive ratioPositive source patch)
    (fun patch => by
      have identity : (virtual.source patch).first.radius = changed.radius (source.val + 1) := prepared.referenceWitness.radiusIdentity source patch
      rw [identity]; exact physicalSmall)
    separated displacements spectral
  have domination := MovingPatchFamilySourceComparison.velocity_envelope_le_zero_radius_series_envelope comparison
    (changed.circulation (source.val + 1)) firstCenter secondCenter (by positivity : 0 ≤ 3 * enlargedLength)
    (by positivity : 0 < gap / 8) baseNonnegative patchDistanceUpper
  dsimp only at velocityActual domination
  have bounded := velocityActual.trans (domination.trans
    (mul_le_mul_of_nonneg_left envelopeBound (by positivity : 0 ≤ gap / 8)))
  let sharp := changed.circulation (source.val + 1) * length ^ 2 / gap ^ 4 *
    (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) *
      (centered + moment + translation + raw) +
      changed.circulation (source.val + 1) * length ^ 2 / gap ^ 5 * observer
  have circulationNonnegative : 0 ≤ changed.circulation (source.val + 1) :=
    (changed.circulation_pos frequencyPositive ratioPositive _).le
  have sharpNonnegative : 0 ≤ sharp := by
    dsimp only [sharp, moment, translation]
    positivity
  have scaledBound : ‖biotSavart (comparison.first.vorticity time) (comparison.firstReceiver time) -
      biotSavart (comparison.second.vorticity time) (comparison.secondReceiver time)‖ ≤
      (1000000000000000 * (baseConstant + 1)) * extent ^ 2 * gap * sharp := by
    apply bounded.trans
    have identity : gap / 8 * (1000000000000000 * (baseConstant + 1) *
        (changed.circulation (source.val + 1) * enlargedLength ^ 2 / gap ^ 4 *
          (1 + changed.location (receiver.val + 1) / changed.location (source.val + 1)) *
            (centered + moment + translation + raw) +
          changed.circulation (source.val + 1) * enlargedLength ^ 2 / gap ^ 5 * observer)) =
        ((1000000000000000 * (baseConstant + 1)) * extent ^ 2 * gap * sharp) / 8 := by
      dsimp only [enlargedLength, sharp]; ring
    rw [identity]
    exact div_le_self (by positivity) (by norm_num)
  have divided := (div_le_div_of_nonneg_right scaledBound receiverPositive.le).trans
    ((div_le_iff₀ receiverPositive).mpr (by
      have multiplied := mul_le_mul_of_nonneg_left gapReceiver
        (show 0 ≤ (1000000000000000 * (baseConstant + 1)) * extent ^ 2 * sharp by positivity)
      convert multiplied using 1; ring))
  have firstFamily : comparison.first = prepared.referenceWitness.trajectory.movingFamily.quadrupoleSubfamily source := rfl
  have secondFamily : comparison.second = prepared.trajectory.movingFamily.quadrupoleSubfamily source := rfl
  rw [firstFamily, secondFamily, firstReceiver, secondReceiver, norm_sub_rev] at scaledBound divided
  constructor
  · simpa only [sharp, translation, observer, raw, centered, moment, first, second, firstCenter, secondCenter, changed,
      norm_sub_rev] using scaledBound
  · simpa only [sharp, translation, observer, raw, centered, moment, first, second, firstCenter, secondCenter, changed,
      norm_sub_rev] using divided

end EulerNonuniqueness.Paper

