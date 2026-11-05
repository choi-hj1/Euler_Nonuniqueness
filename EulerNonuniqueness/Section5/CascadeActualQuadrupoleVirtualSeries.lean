import EulerNonuniqueness.Section5.CascadeActualQuadrupoleComparison
import EulerNonuniqueness.Section5.CascadeForeignReceiverAlignment
import EulerNonuniqueness.Section6.MovingQuadrupoleRelativeSeries
import EulerNonuniqueness.Section6.SignedSourceReceiverGeometry

noncomputable section

open Set Metric Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exists_uniform_actual_foreign_quadrupole_virtual_series :
    ∃ sourceRadius > (0 : ℝ), ∃ constant ≥ (0 : ℝ),
      ∀ scales : Scales, 0 < scales.amplitude → 2 ≤ scales.ratio → 0 < scales.alpha →
      ∀ orbit : SeparatingOrbit, ∀ sectionTime : ℝ,
      ∀ {threshold referenceConstant scaleRoot factor boundaryConstant weight : ℝ},
      threshold ≤ 1 / 8 → 0 ≤ referenceConstant → 1 ≤ scaleRoot → 1 ≤ boundaryConstant →
      0 < factor → factor ≤ 1 → 0 < weight →
      ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {rawCap shapeRadius monitor : ℝ},
      ∀ prepared : CascadeSourcePreparedPair rawCap {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair,
      ∀ {time : ℝ} (inside : time ∈ Icc 0 path.stop),
      ∀ shapes : ∀ label,
        ActualMaterialSpectralShape sourceRadius ((prepared.referenceWitness.trajectory.curve time).2.2 label) ∧
        ActualMaterialSpectralShape sourceRadius ((prepared.trajectory.curve time).2.2 label),
      ∀ receiver : Fin count × Fin 4, ∀ source : Fin count, receiver.1 ≠ source →
      ∀ radius : ℝ, 0 ≤ radius → radius ≤ scales.location (source.val + 1) / 100 →
      (∀ patch, ‖patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source‖ ≤ radius) →
      (∀ patch, ‖patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch -
        quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source‖ ≤ radius) →
      ∀ receiverRadius : ℝ, ∀ receiverNonnegative : 0 ≤ receiverRadius,
      receiverRadius ≤ factor / 409600 * ({scales with frequency := frequency} : Scales).length (receiver.1.val + 1) →
      let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole source
      let comparison : MovingPatchFamilySourceComparison 4 :=
        {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
      let firstCenter := quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source
      let secondCenter := quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source
      let distance := |scales.location (receiver.1.val + 1) - scales.location (source.val + 1)| / 8
      Summable (fun power : ℕ => weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ∧
      (∑' power : ℕ, weight ^ (power + 1) *
        ‖comparison.first.exteriorTaylorCoefficient Finset.univ comparison.firstReceiver comparison.receiverRadius (power + 1) time -
          comparison.second.exteriorTaylorCoefficient Finset.univ comparison.secondReceiver comparison.receiverRadius (power + 1) time‖) ≤
        comparison.quadrupolePointDifferenceEnvelope
          (({scales with frequency := frequency} : Scales).circulation (source.val + 1))
          firstCenter secondCenter radius distance weight +
            2 * ∑ patch : Fin 4, ((comparison.source patch).centroidCorrectionCenterEnvelope distance weight +
              (comparison.source patch).centeredShapeDifferenceEnvelope constant weight) := by
  obtain ⟨sourceRadius, sourcePositive, parameterRadius, parameterPositive, constant, nonnegative, bound⟩ :=
    MovingPatchFamilySourceComparison.quadrupoleCoefficient_exists_centered_weighted_relative_series
  refine ⟨sourceRadius, sourcePositive, constant, nonnegative, ?_⟩
  intro scales amplitudePositive ratioBound alphaPositive orbit sectionTime threshold referenceConstant scaleRoot
    factor boundaryConstant weight thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall weightPositive
  let tolerance := min (1 / 1000 : ℝ) (min (parameterRadius / 4) (1 / (100000 * weight)))
  have tolerancePositive : 0 < tolerance := by dsimp only [tolerance]; positivity
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    scales.eventually_actual_foreign_receiver_alignment amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_radius_lt_length amplitudePositive (by linarith : 1 ≤ scales.ratio) tolerancePositive,
    scales.eventually_length_lt_location ratioBound alphaPositive tolerancePositive]
    with frequency frequencyBound alignment radii lengths
  intro count phase dipoleAngle rawCap shapeRadius monitor prepared path time inside shapes receiver source different
    radius radiusNonnegative radiusSmall firstPositions secondPositions receiverRadius receiverNonnegative receiverSmall
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let original := (prepared.sourceComparison path inside (finProdFinEquiv receiver) shapes).quadrupole source
  let comparison : MovingPatchFamilySourceComparison 4 :=
    {original with receiverRadius := receiverRadius, receiverRadius_nonnegative := receiverNonnegative}
  let firstCenter := quadrupoleCenter prepared.referenceWitness.trajectory.movingFamily.patchMotion time source
  let secondCenter := quadrupoleCenter prepared.trajectory.movingFamily.patchMotion time source
  let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
  let first := comparison.firstReceiver time - firstCenter
  let second := comparison.secondReceiver time - secondCenter
  change radius ≤ changed.location (source.val + 1) / 100 at radiusSmall
  have globalInside : time ∈ Ioo (-(1 : ℝ)) 3 :=
    ⟨by linarith [inside.1], by linarith [inside.2, path.stopBound]⟩
  have firstCenterIdentity (patch : Fin 4) : (comparison.first.patch patch).center time =
      patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time source patch :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have secondCenterIdentity (patch : Fin 4) : (comparison.second.patch patch).center time =
      patchCentroid prepared.trajectory.movingFamily.patchMotion time source patch :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside source patch
  have firstReceiverIdentity : comparison.firstReceiver time =
      patchCentroid prepared.referenceWitness.trajectory.movingFamily.patchMotion time receiver.1 receiver.2 :=
    prepared.referenceWitness.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have secondReceiverIdentity : comparison.secondReceiver time =
      patchCentroid prepared.trajectory.movingFamily.patchMotion time receiver.1 receiver.2 :=
    prepared.trajectory.cascadeCenters_eq_patchCentroid (fun _ => rfl) globalInside receiver.1 receiver.2
  have sourceRadiusIdentity (patch : Fin 4) : (comparison.first.patch patch).radius = changed.radius (source.val + 1) :=
    prepared.referenceWitness.radiusIdentity source patch
  have actualAlignment := alignment count phase dipoleAngle prepared.toCascadeMaterialPreparedPair path time inside receiver source different
  have indexDifferent : receiver.1.val + 1 ≠ source.val + 1 :=
    fun equality => different (Fin.ext (Nat.add_right_cancel equality))
  have gapPositive : 0 < gap := changed.location_distance_pos indexDifferent
  have locations := changed.location_sum_le_three_distance indexDifferent
  change changed.location (receiver.1.val + 1) + changed.location (source.val + 1) ≤ 3 * gap at locations
  have sourceLocation : changed.location (source.val + 1) ≤ 3 * gap := by
    linarith [changed.location_pos (receiver.1.val + 1)]
  have receiverLocation : changed.location (receiver.1.val + 1) ≤ 3 * gap := by
    linarith [changed.location_pos (source.val + 1)]
  have radiusLocation (index : Fin count) : changed.radius (index.val + 1) ≤ tolerance * changed.location (index.val + 1) := by
    have lengthBound : changed.length (index.val + 1) ≤ changed.location (index.val + 1) := by
      have positiveLocation := changed.location_pos (index.val + 1)
      have toleranceUnit : tolerance ≤ 1 := (min_le_left _ _).trans (by norm_num)
      exact (lengths (index.val + 1)).le.trans
        (mul_le_of_le_one_left positiveLocation.le toleranceUnit)
    exact (radii (index.val + 1)).le.trans (mul_le_mul_of_nonneg_left lengthBound tolerancePositive.le)
  have sourceRadiusSmall := radiusLocation source
  have receiverRadiusSmall : comparison.receiverRadius ≤ tolerance * changed.location (receiver.1.val + 1) := by
    change receiverRadius ≤ _
    have scaleSmall : factor / 409600 ≤ 1 := by linarith
    have lengthPositive := changed.length_pos (receiver.1.val + 1)
    have upper : receiverRadius ≤ changed.length (receiver.1.val + 1) :=
      receiverSmall.trans (mul_le_of_le_one_left lengthPositive.le scaleSmall)
    exact upper.trans (lengths (receiver.1.val + 1)).le
  have toleranceSmall : tolerance ≤ 1 / 1000 := min_le_left _ _
  have parameterSmall : tolerance ≤ parameterRadius / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have weightSmall : tolerance * (100000 * weight) ≤ 1 :=
    (le_div_iff₀ (by positivity : (0 : ℝ) < 100000 * weight)).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have sourceRadiusGap : changed.radius (source.val + 1) ≤ 3 * tolerance * gap := by
    nlinarith [mul_le_mul_of_nonneg_left sourceLocation tolerancePositive.le]
  have receiverRadiusGap : comparison.receiverRadius ≤ 3 * tolerance * gap := by
    nlinarith [mul_le_mul_of_nonneg_left receiverLocation tolerancePositive.le]
  have firstBound (patch : Fin 4) : ‖(comparison.first.patch patch).center time - firstCenter‖ ≤ radius := by
    rw [firstCenterIdentity]
    exact firstPositions patch
  have secondBound (patch : Fin 4) : ‖(comparison.second.patch patch).center time - secondCenter‖ ≤ radius := by
    rw [secondCenterIdentity]
    exact secondPositions patch
  have geometry := Section6.signedSourceReceiverGeometry
    ((changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)) first second
    (fun patch => (comparison.first.patch patch).center time - firstCenter)
    (fun patch => (comparison.second.patch patch).center time - secondCenter)
    gapPositive radiusNonnegative (show radius ≤ gap / 16 by linarith)
    (by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])
    (by simpa only [first, firstReceiverIdentity] using actualAlignment.1)
    (by simpa only [second, secondReceiverIdentity] using actualAlignment.2.1)
    firstBound secondBound (fun patch => (comparison.first.patch patch).radius)
    (fun patch => by
      change 2 * (comparison.first.patch patch).radius ≤ gap / 16
      rw [sourceRadiusIdentity]
      nlinarith)
  have displacementIdentity (patch : Fin 4) : first - ((comparison.first.patch patch).center time - firstCenter) =
      comparison.firstReceiver time - (comparison.first.patch patch).center time := by dsimp only [first]; abel
  have secondDisplacementIdentity (patch : Fin 4) : second - ((comparison.second.patch patch).center time - secondCenter) =
      comparison.secondReceiver time - (comparison.second.patch patch).center time := by dsimp only [second]; abel
  have secondLower (patch : Fin 4) : 3 * gap / 4 ≤
      ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ := by
    simpa only [secondDisplacementIdentity] using geometry.2.2.2.2.2 patch
  have sourceParameter (patch : Fin 4) : (comparison.first.patch patch).radius /
      ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ ≤ parameterRadius := by
    rw [sourceRadiusIdentity]
    apply (div_le_iff₀ (lt_of_lt_of_le (by positivity : (0 : ℝ) < 3 * gap / 4) (secondLower patch))).mpr
    nlinarith [mul_le_mul_of_nonneg_right parameterSmall gapPositive.le,
      mul_le_mul_of_nonneg_left (secondLower patch) parameterPositive.le]
  have ratioEight : 8 * weight * comparison.receiverRadius / (gap / 8) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < gap / 8)).mpr
    have weighted := mul_le_mul_of_nonneg_left receiverRadiusGap weightPositive.le
    have scaled := mul_le_mul_of_nonneg_right weightSmall gapPositive.le
    nlinarith
  have ratioFour : 4 * weight * comparison.receiverRadius / (gap / 8) < 1 := by
    have receiverNonnegative := comparison.receiverRadius_nonnegative
    have eightNonnegative : 0 ≤ 8 * weight * comparison.receiverRadius / (gap / 8) := by positivity
    have identity : 4 * weight * comparison.receiverRadius / (gap / 8) =
        (8 * weight * comparison.receiverRadius / (gap / 8)) / 2 := by ring
    rw [identity]
    linarith
  have shapeRatio (patch : Fin 4) : 96 * weight * comparison.receiverRadius /
      ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ ≤ 1 / 2 := by
    apply (div_le_iff₀ (lt_of_lt_of_le (by positivity : (0 : ℝ) < 3 * gap / 4) (secondLower patch))).mpr
    have weighted := mul_le_mul_of_nonneg_left receiverRadiusGap weightPositive.le
    have scaled := mul_le_mul_of_nonneg_right weightSmall gapPositive.le
    linarith [secondLower patch]
  have actual := bound comparison
    (fun patch => mem_ball_zero_iff.mpr (shapes (finProdFinEquiv (source, patch))).1.small)
    (fun patch => mem_ball_zero_iff.mpr (shapes (finProdFinEquiv (source, patch))).2.small)
    (fun patch => (shapes (finProdFinEquiv (source, patch))).1.centroid)
    (fun patch => (shapes (finProdFinEquiv (source, patch))).2.centroid)
    (fun patch => prepared.sourceComparison_first_true_centers path inside (finProdFinEquiv receiver) shapes (finProdFinEquiv (source, patch)))
    (changed.circulation (source.val + 1)) firstCenter secondCenter
    (prepared.sourceComparison_quadrupole_masses path inside (finProdFinEquiv receiver) shapes
      amplitudePositive (zero_lt_one.trans_le frequencyBound) (by change 0 < scales.ratio; linarith) source)
    radius (3 * gap / 8) (gap / 8) weight (fun _ => gap / 2)
    radiusNonnegative (by positivity) (by positivity) weightPositive.le geometry.1 firstBound secondBound geometry.2.1
    (fun _ => by positivity)
    (fun patch => by simpa only [displacementIdentity] using geometry.2.2.1 patch)
    (fun patch => by simpa only [secondDisplacementIdentity] using geometry.2.2.2.1 patch)
    (fun patch => by simpa only [MovingPatchSourceComparison.displacementDifference,
      MovingPatchFamilySourceComparison.source, displacementIdentity, secondDisplacementIdentity] using geometry.2.2.2.2.1 patch)
    sourceParameter ratioFour (ratioEight.trans_lt (by norm_num))
    (fun patch => (shapeRatio patch).trans_lt (by norm_num))
  refine ⟨actual.1, actual.2.trans ?_⟩
  apply add_le_add_left
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro patch _
  have denominatorBound : (1 - 8 * weight * comparison.receiverRadius / (gap / 8))⁻¹ ≤ 2 := by
    have estimate := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - 8 * weight * comparison.receiverRadius / (gap / 8) by linarith)
    norm_num at estimate
    exact estimate
  have shapeDenominatorBound : (1 - 96 * weight * comparison.receiverRadius /
      ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖)⁻¹ ≤ 2 := by
    have estimate := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2)
      (show 1 / 2 ≤ 1 - 96 * weight * comparison.receiverRadius /
        ‖comparison.secondReceiver time - (comparison.second.patch patch).center time‖ by linarith [shapeRatio patch])
    norm_num at estimate
    exact estimate
  have centerNonnegative : 0 ≤ (comparison.source patch).centroidCorrectionCenterEnvelope (gap / 8) weight := by
    unfold MovingPatchSourceComparison.centroidCorrectionCenterEnvelope
    positivity
  have shapeNonnegative : 0 ≤ (comparison.source patch).centeredShapeDifferenceEnvelope constant weight := by
    have budget := (comparison.source patch).spectralDifferenceBudget_nonnegative
    unfold MovingPatchSourceComparison.centeredShapeDifferenceEnvelope
    positivity
  exact (add_le_add (mul_le_mul_of_nonneg_left denominatorBound centerNonnegative)
    (mul_le_mul_of_nonneg_left shapeDenominatorBound shapeNonnegative)).trans_eq (by
      change (comparison.source patch).centroidCorrectionCenterEnvelope (gap / 8) weight * 2 +
        (comparison.source patch).centeredShapeDifferenceEnvelope constant weight * 2 =
          2 * ((comparison.source patch).centroidCorrectionCenterEnvelope (gap / 8) weight +
            (comparison.source patch).centeredShapeDifferenceEnvelope constant weight)
      ring)

end EulerNonuniqueness.Paper

