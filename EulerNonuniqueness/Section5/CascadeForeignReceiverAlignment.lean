import EulerNonuniqueness.Section4.ReferenceMaterialPairVectorDrift
import EulerNonuniqueness.Section5.CascadeMaterialAnchorVectorDrift
import EulerNonuniqueness.Section5.CascadeStoppedMaterialGeometry

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000

theorem Scales.eventually_actual_foreign_receiver_alignment (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
      ∀ {shapeRadius monitor : ℝ},
      ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
        threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
      ∀ path : CascadeInternallyStoppedPath prepared, ∀ time ∈ Icc 0 path.stop,
      ∀ receiver : Fin count × Fin 4, ∀ source : Fin count, receiver.1 ≠ source →
      let changed : Scales := {scales with frequency := frequency}
      let ideal := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
      let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
      let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
      let second := prepared.trajectory.movingFamily.patchMotion
      ‖(patchCentroid first time receiver.1 receiver.2 - quadrupoleCenter first time source) - ideal‖ ≤ 3 * gap / 16 ∧
      ‖(patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source) - ideal‖ ≤ 3 * gap / 16 ∧
      (∀ patch, ‖patchCentroid first time source patch - quadrupoleCenter first time source‖ ≤ changed.location (source.val + 1) / 100) ∧
      (∀ patch, ‖patchCentroid second time source patch - quadrupoleCenter second time source‖ ≤ changed.location (source.val + 1) / 100) := by
  filter_upwards [scales.eventually_reference_material_pair_vector_drift amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative,
    scales.eventually_material_cascade_anchor_vector_drift amplitudePositive ratioBound alphaPositive orbit sectionTime
      factorPositive factorSmall (thresholdSmall.trans (by norm_num)) rootOne boundaryOne,
    scales.eventually_universal_reference_mechanical_data amplitudePositive ratioBound alphaPositive
      thresholdSmall referenceNonnegative,
    scales.eventually_length_lt_location ratioBound alphaPositive (by norm_num : (0 : ℝ) < 1 / 300)]
    with frequency referenceDrift alternativeDrift mechanical lengths
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver source different
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let first := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let second := prepared.trajectory.movingFamily.patchMotion
  let ideal := (changed.location (receiver.1.val + 1) : ℂ) - (changed.location (source.val + 1) : ℂ)
  let gap := |changed.location (receiver.1.val + 1) - changed.location (source.val + 1)|
  have referenceInside : time ∈ Icc (0 : ℝ) 2 := ⟨inside.1, by linarith [inside.2, path.stopBound]⟩
  have lengthSmall (index : Fin count) : 3 * changed.length (index.val + 1) ≤ changed.location (index.val + 1) / 100 := by
    have actual : changed.length (index.val + 1) ≤ (1 / 300 : ℝ) * changed.location (index.val + 1) :=
      (lengths (index.val + 1)).le
    linarith
  have firstExtent (index : Fin count) (patch : Fin 4) :
      ‖patchCentroid first time index patch - quadrupoleCenter first time index‖ ≤ changed.location (index.val + 1) / 100 :=
    ((mechanical first prepared.referenceWitness.evolution prepared.referenceWitness.coarse time referenceInside index).1.centroidsBounded patch).trans
      (lengthSmall index)
  have secondExtent (index : Fin count) (patch : Fin 4) :
      ‖patchCentroid second time index patch - quadrupoleCenter second time index‖ ≤ changed.location (index.val + 1) / 100 :=
    (path.centroid_extent inside index patch).le
  have actualAlternative := alternativeDrift count phase dipoleAngle prepared path.stop path.stopPositive.le path.stopBound
    path.internalClosed
    (fun current member label => (path.externalMonitors current member (.extent label)).le)
    (fun current member left right => (path.externalMonitors current member (.lower left right)).le)
    (fun current member left right => (path.externalMonitors current member (.upper left right)).le)
    (fun current member index => (path.externalMonitors current member (.anchor index)).le)
    time inside receiver.1 source
  have actualReference := referenceDrift count (fun index => phase (index.val + 1)) prepared.referenceWitness
    time referenceInside receiver.1 source different
  change ‖(quadrupoleCenter first time receiver.1 - quadrupoleCenter first time source) - ideal‖ ≤ gap / 8 at actualReference
  change ‖(quadrupoleCenter second time receiver.1 - quadrupoleCenter second time source) - ideal‖ ≤ gap / 8 at actualAlternative
  have indexDifferent : receiver.1.val + 1 ≠ source.val + 1 :=
    fun equality => different (Fin.ext (Nat.add_right_cancel equality))
  have locations := changed.location_sum_le_three_distance indexDifferent
  change changed.location (receiver.1.val + 1) + changed.location (source.val + 1) ≤ 3 * gap at locations
  have sourcePositive := changed.location_pos (source.val + 1)
  have gapNonnegative : 0 ≤ gap := abs_nonneg _
  have receiverExtent : changed.location (receiver.1.val + 1) / 100 ≤ gap / 16 := by
    linarith
  refine ⟨?_, ?_, firstExtent source, secondExtent source⟩
  · change ‖(patchCentroid first time receiver.1 receiver.2 - quadrupoleCenter first time source) - ideal‖ ≤ 3 * gap / 16
    have identity : (patchCentroid first time receiver.1 receiver.2 - quadrupoleCenter first time source) - ideal =
        (patchCentroid first time receiver.1 receiver.2 - quadrupoleCenter first time receiver.1) +
          ((quadrupoleCenter first time receiver.1 - quadrupoleCenter first time source) - ideal) := by abel
    rw [identity]
    have triangle := norm_add_le
      (patchCentroid first time receiver.1 receiver.2 - quadrupoleCenter first time receiver.1)
      ((quadrupoleCenter first time receiver.1 - quadrupoleCenter first time source) - ideal)
    linarith [firstExtent receiver.1 receiver.2]
  · change ‖(patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source) - ideal‖ ≤ 3 * gap / 16
    have identity : (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time source) - ideal =
        (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time receiver.1) +
          ((quadrupoleCenter second time receiver.1 - quadrupoleCenter second time source) - ideal) := by abel
    rw [identity]
    have triangle := norm_add_le
      (patchCentroid second time receiver.1 receiver.2 - quadrupoleCenter second time receiver.1)
      ((quadrupoleCenter second time receiver.1 - quadrupoleCenter second time source) - ideal)
    linarith [secondExtent receiver.1 receiver.2]

end EulerNonuniqueness.Paper
