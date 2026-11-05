import EulerNonuniqueness.Section5.CascadeIndividualSourceInputContinuity
import EulerNonuniqueness.Section5.CascadeQuadrupoleForeignClearance
import EulerNonuniqueness.Section6.PaperRelativeLeadingStrainSum
import EulerNonuniqueness.Section3.FinitePatchRestriction

noncomputable section

open Set Filter
open scoped Topology BigOperators

namespace EulerNonuniqueness.Paper

private theorem sum_erase_eq_coarser_adjacent_older
    {count : ℕ} (receiver adjacent : Fin count) (next : receiver.val + 1 = adjacent.val)
    (values : Fin count → ℝ × ℝ) :
    (∑ source ∈ Finset.univ.erase receiver, values source) =
      (∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), values source) +
        values adjacent +
        ∑ source ∈ Finset.univ.filter (fun source : Fin count => adjacent.val < source.val), values source := by
  classical
  let coarser := Finset.univ.filter (fun source : Fin count => source.val < receiver.val)
  let older := Finset.univ.filter (fun source : Fin count => adjacent.val < source.val)
  have disjoint : Disjoint coarser (insert adjacent older) := by
    apply Finset.disjoint_left.mpr
    intro source coarseMember otherMember
    have below := (Finset.mem_filter.mp coarseMember).2
    rcases Finset.mem_insert.mp otherMember with same | oldMember
    · subst source
      omega
    · have above := (Finset.mem_filter.mp oldMember).2
      omega
  have adjacentAbsent : adjacent ∉ older := by simp only [older, Finset.mem_filter, lt_self_iff_false, and_false, not_false_eq_true]
  have identity : Finset.univ.erase receiver = coarser ∪ insert adjacent older := by
    ext source
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, coarser,
      Finset.mem_filter, true_and, Finset.mem_insert, older]
    constructor
    · intro different
      by_cases below : source.val < receiver.val
      · exact Or.inl below
      · by_cases same : source = adjacent
        · exact Or.inr (Or.inl same)
        · have unequal : source.val ≠ receiver.val := by
            intro equal
            exact different (Fin.ext equal)
          have notAdjacent : source.val ≠ adjacent.val := by
            intro equal
            exact same (Fin.ext equal)
          exact Or.inr (Or.inr (by omega))
    · rintro (below | same | above)
      · intro equal
        subst source
        exact (lt_irrefl receiver.val) below
      · subst source
        intro equal
        have sameValues := congrArg Fin.val equal
        omega
      · intro equal
        subst source
        omega
  rw [identity, Finset.sum_union disjoint, Finset.sum_insert adjacentAbsent]
  change _ = _
  abel

theorem Scales.eventually_cascade_leading_three_way_split (scales : Scales)
    (amplitudePositive : 0 < scales.amplitude) (ratioBound : 2 ≤ scales.ratio)
    (alphaPositive : 0 < scales.alpha) (orbit : SeparatingOrbit) (sectionTime : ℝ)
    {threshold referenceConstant scaleRoot factor boundaryConstant : ℝ}
    (thresholdSmall : threshold ≤ 1 / 8) (referenceNonnegative : 0 ≤ referenceConstant)
    (rootOne : 1 ≤ scaleRoot) (boundaryOne : 1 ≤ boundaryConstant)
    (factorPositive : 0 < factor) (factorSmall : factor ≤ 1) :
    ∀ᶠ frequency : ℝ in atTop, ∀ count : ℕ, ∀ phase dipoleAngle : ℕ → ℝ,
    ∀ {shapeRadius monitor : ℝ},
    ∀ prepared : CascadeMaterialPreparedPair {scales with frequency := frequency} orbit sectionTime phase dipoleAngle
      threshold referenceConstant scaleRoot shapeRadius factor monitor boundaryConstant count,
    ∀ path : CascadeInternallyStoppedPath prepared, ∀ receiver adjacent : Fin count,
    receiver.val + 1 = adjacent.val →
    let changed : Scales := {scales with frequency := frequency}
    let input := fun source => relativeBlockSourceShapeInput changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference receiver source
    let leading := fun time => quadrupoleRelativeLeadingStrain changed prepared.trajectory.movingFamily.patchMotion
      prepared.reference time receiver
    let coarser := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => source.val < receiver.val), input source time
    let older := fun time => ∑ source ∈ Finset.univ.filter (fun source : Fin count => adjacent.val < source.val), input source time
    ContinuousOn leading (Icc 0 path.stop) ∧ ContinuousOn coarser (Icc 0 path.stop) ∧
    ContinuousOn (input adjacent) (Icc 0 path.stop) ∧ ContinuousOn older (Icc 0 path.stop) ∧
    ∀ time ∈ Icc 0 path.stop, leading time = coarser time + input adjacent time + older time := by
  classical
  filter_upwards [scales.eventually_cascade_individual_source_input_continuous amplitudePositive ratioBound alphaPositive
      orbit sectionTime thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall,
    scales.eventually_cascade_quadrupole_foreign_clearance amplitudePositive ratioBound alphaPositive orbit sectionTime
      thresholdSmall referenceNonnegative rootOne boundaryOne factorPositive factorSmall]
    with frequency regular clearance
  intro count phase dipoleAngle shapeRadius monitor prepared path receiver adjacent next
  let changed : Scales := {scales with frequency := frequency}
  let alternative := prepared.trajectory.movingFamily.patchMotion
  let reference := prepared.reference
  let input := fun source => relativeBlockSourceShapeInput changed alternative reference receiver source
  let leading := fun time => quadrupoleRelativeLeadingStrain changed alternative reference time receiver
  have different : receiver ≠ adjacent := by
    intro equal
    have sameValues := congrArg Fin.val equal
    omega
  have sumIdentity (time : ℝ) (inside : time ∈ Icc 0 path.stop) :
      leading time = ∑ source ∈ Finset.univ.erase receiver, input source time := by
    let gap := changed.location (receiver.val + 1) / 24
    have gapPositive : 0 < gap := div_pos (changed.location_pos _) (by norm_num)
    have actual := clearance count phase dipoleAngle prepared path time inside receiver
    have commonLower (source : Fin count) (member : source ∈ Finset.univ.erase receiver) :
        gap ≤ |changed.location (receiver.val + 1) - changed.location (source.val + 1)| / 8 := by
      have differentValues : receiver.val + 1 ≠ source.val + 1 := fun equality =>
        (Finset.mem_erase.mp member).1 (Fin.ext (Nat.add_right_cancel equality).symm)
      have spacing := changed.location_sum_le_three_distance differentValues
      dsimp only [gap]
      linarith only [spacing, changed.location_pos (source.val + 1)]
    have identity := quadrupoleRelativeLeadingStrain_eq_sum_actual_sources path.evolution
      (prepared.referenceWitness.evolution.mono (show path.stop ≤ 2 by linarith only [path.stopBound])) inside receiver
      gapPositive gapPositive
      (fun source member patch position inDomain => (commonLower source member).trans (actual.2 source member patch position inDomain))
      (fun source member patch position inDomain => (commonLower source member).trans (actual.1 source member patch position inDomain))
    simpa only [leading, input, alternative, reference, prepared.referenceIdentity] using identity
  have sumContinuous : ContinuousOn (fun time => ∑ source ∈ Finset.univ.erase receiver, input source time) (Icc 0 path.stop) := by
    apply continuousOn_finset_sum
    intro source member
    exact regular count phase dipoleAngle prepared path receiver source ((Finset.mem_erase.mp member).1).symm
  refine ⟨sumContinuous.congr sumIdentity, ?_, regular count phase dipoleAngle prepared path receiver adjacent different, ?_, ?_⟩
  · apply continuousOn_finset_sum
    intro source member
    have below := (Finset.mem_filter.mp member).2
    exact regular count phase dipoleAngle prepared path receiver source (by intro equal; subst source; exact (lt_irrefl receiver.val) below)
  · apply continuousOn_finset_sum
    intro source member
    have above := (Finset.mem_filter.mp member).2
    exact regular count phase dipoleAngle prepared path receiver source (by
      intro equal
      have sameValues := congrArg Fin.val equal
      omega)
  · intro time inside
    exact (sumIdentity time inside).trans (sum_erase_eq_coarser_adjacent_older receiver adjacent next (fun source => input source time))

end EulerNonuniqueness.Paper
