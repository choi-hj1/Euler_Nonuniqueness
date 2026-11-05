import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic

noncomputable section

namespace EulerNonuniqueness.General

theorem graded_chart_interaction_le (firstUnstable firstStable secondUnstable secondStable reference : ℝ)
    (referenceBound : |secondUnstable| + |secondStable| ≤ reference) :
    (|firstStable| + |secondStable|) * |firstUnstable - secondUnstable| +
      (|firstUnstable| + |secondUnstable| + |firstStable| + |secondStable|) * |firstStable - secondStable| ≤
      (|firstUnstable - secondUnstable| + |firstStable - secondStable| + 2 * reference) *
        (|firstUnstable - secondUnstable| + |firstStable - secondStable|) := by
  have unstable := abs_sub_le firstUnstable secondUnstable 0
  have stable := abs_sub_le firstStable secondStable 0
  simp only [sub_zero] at unstable stable
  have firstBound : |firstStable| + |secondStable| ≤
      |firstUnstable - secondUnstable| + |firstStable - secondStable| + 2 * reference := by
    linarith [abs_nonneg secondUnstable, abs_nonneg (firstUnstable - secondUnstable)]
  have secondBound : |firstUnstable| + |secondUnstable| + |firstStable| + |secondStable| ≤
      |firstUnstable - secondUnstable| + |firstStable - secondStable| + 2 * reference := by linarith
  have bound := add_le_add
    (mul_le_mul_of_nonneg_right firstBound (abs_nonneg (firstUnstable - secondUnstable)))
    (mul_le_mul_of_nonneg_right secondBound (abs_nonneg (firstStable - secondStable)))
  exact bound.trans_eq (by ring)

end EulerNonuniqueness.General
