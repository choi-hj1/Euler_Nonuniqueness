import EulerNonuniqueness.Section5.CascadeStatement
import EulerNonuniqueness.Section6.MovingComplexMomentContinuity
import EulerNonuniqueness.General.FirstContact

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem FiniteMovingPatchFamily.pairCenterDistance_continuous {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (index : Fin count) :
    Continuous (fun time => pairCenterDistance family.patchMotion time index) := by
  exact (((family.patchCentroid_continuous index 0).add (family.patchCentroid_continuous index 3)).div_const 2 |>.sub
    (((family.patchCentroid_continuous index 1).add (family.patchCentroid_continuous index 2)).div_const 2)).norm

theorem FiniteMovingPatchFamily.exists_firstSeparationTime_of_crossing {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales) (orbit : SeparatingOrbit)
    (sectionTime : ℝ) (index : Fin count) {horizon : ℝ} (horizonNonnegative : 0 ≤ horizon)
    (initial : pairCenterDistance family.patchMotion 0 index ≤
      separationRadius orbit sectionTime * scales.length (index.val + 1))
    (crossed : separationRadius orbit sectionTime * scales.length (index.val + 1) <
      pairCenterDistance family.patchMotion horizon index) :
    ∃ time ∈ Icc 0 horizon,
      FirstSeparationTime scales orbit sectionTime family.patchMotion index time ∧
      ∀ earlier ∈ Ico 0 time, pairCenterDistance family.patchMotion earlier index <
        separationRadius orbit sectionTime * scales.length (index.val + 1) := by
  obtain ⟨time, inside, equality, before⟩ := exists_first_zero_of_initial_nonpos_of_positive
    horizonNonnegative ((family.pairCenterDistance_continuous index).sub continuous_const).continuousOn
    (sub_nonpos.mpr initial) (sub_pos.mpr crossed)
  refine ⟨time, inside, ⟨inside.1, sub_eq_zero.mp equality, ?_⟩, ?_⟩
  · intro earlier nonnegative earlierBound
    exact ne_of_lt (sub_neg.mp (before earlier nonnegative earlierBound))
  · intro earlier earlierInside
    exact sub_neg.mp (before earlier earlierInside.1 earlierInside.2)

theorem FirstSeparationTime.unique {count : ℕ} {scales : Scales} {orbit : SeparatingOrbit}
    {sectionTime : ℝ} {motion : PatchMotion count} {index : Fin count} {first second : ℝ}
    (firstHit : FirstSeparationTime scales orbit sectionTime motion index first)
    (secondHit : FirstSeparationTime scales orbit sectionTime motion index second) : first = second := by
  apply le_antisymm
  · by_contra failure
    exact firstHit.2.2 second secondHit.1 (lt_of_not_ge failure) secondHit.2.1
  · by_contra failure
    exact secondHit.2.2 first firstHit.1 (lt_of_not_ge failure) firstHit.2.1

end EulerNonuniqueness.Paper
