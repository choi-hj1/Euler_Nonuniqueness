import EulerNonuniqueness.Section6.SourcePacketFinerVectorActualDrive
import EulerNonuniqueness.General.ErasedAdjacentSum
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6 EulerNonuniqueness.General

theorem Scales.eventually_actual_relative_leading_adjacent_remainder (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio) (alphaPositive : 0 < scales.alpha)
    (ratioPower : 4 < scales.ratio ^ scales.alpha) {tolerance : ℝ} (tolerancePositive : 0 < tolerance)
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
      ∀ receiver adjacent : Fin count, receiver.val + 1 = adjacent.val →
      let changed : Scales := {scales with frequency := frequency}
      let alternative := prepared.trajectory.movingFamily.patchMotion
      let reference := prepared.reference
      ‖quadrupoleRelativeLeadingStrain changed alternative reference time receiver -
        ((∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
          relativeBlockSourceShapeInput changed alternative reference receiver source time) +
          relativeBlockSourceShapeInput changed alternative reference receiver adjacent time)‖ ≤
        tolerance * changed.seed (receiver.val + 1) := by
  filter_upwards [scales.eventually_actual_finer_source_vector_seed_bound amplitudePositive ratioBound alphaPositive
      ratioPower tolerancePositive orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency fine clearance
  intro count phase dipoleAngle shapeRadius monitor prepared path time inside receiver adjacent adjacentIdentity
  dsimp only
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.referenceWitness.trajectory.movingFamily.patchMotion
  let gap := changed.location (receiver.val + 1) / 24
  have gapPositive : 0 < gap := div_pos (changed.location_pos _) (by norm_num)
  have actual := clearance count phase dipoleAngle prepared path time inside receiver
  have commonLower (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
      gap ≤ |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 := by
    have different : receiver.val + 1 ≠ source.val + 1 := fun equality =>
      (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
    have spacing := changed.location_sum_le_three_distance different
    dsimp only [gap]
    linarith [changed.location_pos (source.val + 1)]
  have alternativeSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
      position ∈ alternative.domain time source patch → gap ≤ ‖quadrupoleCenter alternative time receiver - position‖ := by
    intro source member patch position domainMember
    exact (commonLower source member).trans (actual.2 source member patch position domainMember)
  have referenceSeparated : ∀ source ∈ Finset.univ.erase receiver, ∀ patch position,
      position ∈ reference.domain time source patch → gap ≤ ‖quadrupoleCenter reference time receiver - position‖ := by
    intro source member patch position domainMember
    exact (commonLower source member).trans (actual.1 source member patch position domainMember)
  have leading := quadrupoleRelativeLeadingStrain_eq_sum_actual_sources path.evolution
    (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith [path.stopBound])) inside receiver
    gapPositive gapPositive alternativeSeparated referenceSeparated
  have split := sum_erase_eq_lower_add_adjacent_add_finer receiver adjacent adjacentIdentity
    (fun source => relativeBlockSourceShapeInput changed alternative reference receiver source time)
  rw [split] at leading
  have remainder : quadrupoleRelativeLeadingStrain changed alternative reference time receiver -
      ((∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val),
        relativeBlockSourceShapeInput changed alternative reference receiver source time) +
        relativeBlockSourceShapeInput changed alternative reference receiver adjacent time) =
      ∑ source ∈ Finset.univ.filter (fun source : Fin count => receiver.val + 2 ≤ source.val),
        relativeBlockSourceShapeInput changed alternative reference receiver source time := by
    rw [leading, add_sub_cancel_left]
  rw [prepared.referenceIdentity, remainder]
  have bound := fine count phase dipoleAngle prepared path time inside receiver
  rw [prepared.referenceIdentity] at bound
  exact bound

end EulerNonuniqueness.Paper
