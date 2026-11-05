import EulerNonuniqueness.Section5.CascadeRawSourceWeightedFeedback
import EulerNonuniqueness.Section5.CascadeRelativeFirstMomentHistory
import EulerNonuniqueness.Section5.CascadeMaterialInitialExtent
import EulerNonuniqueness.Section5.CascadeBlockExtentCentroids
import EulerNonuniqueness.Section4.InitialReferenceDiskSeparation
import EulerNonuniqueness.Section6.SourcePacketInitialNeutral

noncomputable section

open Set
open scoped BigOperators

namespace EulerNonuniqueness.Paper.CascadeSourcePreparedPair

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

variable {rawCap : ℝ} {scales : Scales} {orbit : SeparatingOrbit} {sectionTime : ℝ}
  {phase dipoleAngle : ℕ → ℝ}
  {threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant : ℝ} {count : ℕ}

theorem initial_raw_source_shape_zero
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count) (index : Fin count) (patch : Fin 4) :
    prepared.rawSourceShapeBudget 0 index patch = 0 := by
  have rawEqual : prepared.referenceWitness.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) 0 =
      prepared.trajectory.spectralCoordinate (finProdFinEquiv (index, patch)) 0 := by
    simp only [MovingCentroidGaugeTrajectory.spectralCoordinate,
      prepared.referenceWitness.trajectory.initial_identity, prepared.trajectory.initial_identity]
    rfl
  with_reducible_and_instances
    simp only [rawSourceShapeBudget, rawEqual, sub_self, norm_zero, mul_zero, add_zero]

/-- The entire initial sharp source state is bounded uniformly over the array, including its terminal packet. -/
theorem initial_sharp_state_bound
    (prepared : CascadeSourcePreparedPair rawCap scales orbit sectionTime phase dipoleAngle threshold referenceConstant
      scaleRoot shapeRadius factor monitor boundaryConstant count)
    (path : CascadeInternallyStoppedPath prepared.toCascadeMaterialPreparedPair)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio) (thresholdSmall : threshold ≤ 1 / 2)
    {bound : ℝ} (boundThree : 3 ≤ bound)
    (positiveBound : ‖orbit.positive sectionTime‖ ≤ bound)
    (negativeBound : ‖orbit.negative sectionTime‖ ≤ bound) (index : Fin count) :
    prepared.rawSourceCenteredState 0 index +
      ‖relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index 0‖ +
      ‖quadrupoleCenter prepared.trajectory.movingFamily.patchMotion 0 index -
        quadrupoleCenter prepared.reference 0 index‖ / scales.location (index.val + 1) +
      (∑ patch : Fin 4, prepared.rawSourceShapeBudget 0 index patch) ≤ bound + 2 := by
  let material := prepared.toCascadeMaterialPreparedPair
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let motion := prepared.trajectory.movingFamily.patchMotion
  have referenceData := prepared.referenceWitness.evolution.reference_initial_center_and_asymmetry
    (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index
  have referenceCenter : quadrupoleCenter reference 0 index = (scales.location (index.val + 1) : ℂ) := referenceData.1
  have initialNeutral : centroidAsymmetry motion 0 index = 0 :=
    path.source_packet_initial_neutral amplitudePositive frequencyPositive ratioPositive thresholdSmall index
  have actualCenter : quadrupoleCenter motion 0 index = (scales.location (index.val + 1) : ℂ) := by
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt index.isLt) with nonterminal | terminal
    · rw [material.nonterminal_initial_center index nonterminal, material.referenceIdentity]
      exact referenceCenter
    · have centroids := path.evolution.cascade_terminal_initial_centroid path.stopPositive.le amplitudePositive
        frequencyPositive ratioPositive material.commonInitial index terminal
      dsimp only [motion, quadrupoleCenter]
      rw [Fin.sum_univ_four, centroids 0, centroids 1, centroids 2, centroids 3]
      simp only [separatingInitialCenter, Fin.reduceEq, ↓reduceIte]
      rw [show index.val + 1 = count by omega]
      ring
  have initialMoment : relativeNormalizedFirstMoment scales motion material.reference index 0 = 0 := by
    rw [relativeNormalizedFirstMoment, material.referenceIdentity]
    change _ • (centroidAsymmetry motion 0 index - centroidAsymmetry reference 0 index) = 0
    rw [initialNeutral, referenceData.2, sub_self, smul_zero]
  have actualExtents := material.initial_extent_bound thresholdSmall boundThree positiveBound negativeBound index
  have actualExtent (patch : Fin 4) :
      ‖patchCentroid motion 0 index patch - quadrupoleCenter motion 0 index‖ ≤ bound * scales.length (index.val + 1) := by
    have estimate := (norm_le_pi_norm (prepared.trajectory.blockExtentVector index 0) patch).trans actualExtents
    rw [prepared.trajectory.blockExtentVector_eq_centroid_offset (fun _ => rfl) (by constructor <;> norm_num) index patch] at estimate
    exact estimate
  have referenceExtent (patch : Fin 4) :
      ‖patchCentroid reference 0 index patch - quadrupoleCenter reference 0 index‖ ≤ 2 * scales.length (index.val + 1) := by
    rw [referenceCenter, prepared.referenceWitness.evolution.reference_initial_centroid
      (by norm_num : (0 : ℝ) ≤ 2) amplitudePositive frequencyPositive ratioPositive prepared.referenceWitness.initial index patch]
    exact initialDiskCenter_offset_bound scales _ _ _
      ((prepared.referenceWitness.initial index).1.trans thresholdSmall) patch
  have normBound : ‖(fun patch => patchCentroid reference 0 index patch - quadrupoleCenter reference 0 index) -
      (fun patch => patchCentroid motion 0 index patch - quadrupoleCenter motion 0 index)‖ ≤
      (bound + 2) * scales.length (index.val + 1) := by
    have boundNonnegative : 0 ≤ bound := by linarith only [boundThree]
    apply (pi_norm_le_iff_of_nonneg
      (mul_nonneg (add_nonneg boundNonnegative (by norm_num)) (scales.length_pos (index.val + 1)).le)).mpr
    intro patch
    have triangle := norm_sub_le
      (patchCentroid reference 0 index patch - quadrupoleCenter reference 0 index)
      (patchCentroid motion 0 index patch - quadrupoleCenter motion 0 index)
    change ‖(patchCentroid reference 0 index patch - quadrupoleCenter reference 0 index) -
      (patchCentroid motion 0 index patch - quadrupoleCenter motion 0 index)‖ ≤ _
    nlinarith only [triangle, actualExtent patch, referenceExtent patch]
  have centeredBound : prepared.rawSourceCenteredState 0 index ≤ bound + 2 := by
    apply (div_le_iff₀ (scales.length_pos _)).mpr
    exact normBound
  have rawZero : (∑ patch : Fin 4, prepared.rawSourceShapeBudget 0 index patch) = 0 := by
    simp only [prepared.initial_raw_source_shape_zero index, Finset.sum_const_zero]
  have centerZero : quadrupoleCenter prepared.trajectory.movingFamily.patchMotion 0 index -
      quadrupoleCenter prepared.reference 0 index = 0 := by
    rw [material.referenceIdentity]
    change quadrupoleCenter motion 0 index - quadrupoleCenter reference 0 index = 0
    rw [actualCenter, referenceCenter, sub_self]
  rw [show relativeNormalizedFirstMoment scales prepared.trajectory.movingFamily.patchMotion prepared.reference index 0 = 0 from initialMoment,
    centerZero, rawZero]
  simpa only [norm_zero, zero_div, add_zero] using centeredBound

end EulerNonuniqueness.Paper.CascadeSourcePreparedPair
