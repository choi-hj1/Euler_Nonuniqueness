import Mathlib

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem deriv_smoothTransition_eq_zero_of_negative {position : ℝ} (negative : position < 0) :
    deriv Real.smoothTransition position = 0 := by
  have equality : Real.smoothTransition =ᶠ[𝓝 position] fun _ => (0 : ℝ) := by
    filter_upwards [eventually_lt_nhds negative] with point inside
    exact Real.smoothTransition.zero_of_nonpos inside.le
  rw [equality.deriv_eq]
  exact deriv_const _ _

theorem deriv_smoothTransition_eq_zero_of_one_lt {position : ℝ} (after : 1 < position) :
    deriv Real.smoothTransition position = 0 := by
  have equality : Real.smoothTransition =ᶠ[𝓝 position] fun _ => (1 : ℝ) := by
    filter_upwards [eventually_gt_nhds after] with point inside
    exact Real.smoothTransition.one_of_one_le inside.le
  rw [equality.deriv_eq]
  exact deriv_const _ _

theorem support_deriv_smoothTransition : Function.support (deriv Real.smoothTransition) ⊆ Icc 0 1 := by
  intro position nonzero
  constructor
  · by_contra before
    exact nonzero (deriv_smoothTransition_eq_zero_of_negative (lt_of_not_ge before))
  · by_contra after
    exact nonzero (deriv_smoothTransition_eq_zero_of_one_lt (lt_of_not_ge after))

theorem exists_bound_deriv_smoothTransition :
    ∃ bound : ℝ, 1 ≤ bound ∧ ∀ position, ‖deriv Real.smoothTransition position‖ ≤ bound := by
  have compact : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc support_deriv_smoothTransition
  have continuous : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).continuous_deriv (by simp)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuous continuous
  exact ⟨max bound 1, le_max_right _ _, fun position => (bounded position).trans (le_max_left _ _)⟩

end EulerNonuniqueness
