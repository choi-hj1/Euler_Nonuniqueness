import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Set

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_history_le_of_exists_hasDerivAt
    {curve : ℝ → Space} {horizon bound : ℝ}
    (actual : ∀ time ∈ Icc 0 horizon, ∃ velocity : Space,
      HasDerivAt curve velocity time ∧ ‖velocity‖ ≤ bound) :
    ∀ time ∈ Icc 0 horizon, ‖curve time - curve 0‖ ≤ bound * time := by
  have continuous : ContinuousOn curve (Icc 0 horizon) := by
    intro time inside
    obtain ⟨velocity, derivative, _⟩ := actual time inside
    exact derivative.continuousAt.continuousWithinAt
  have derivatives (time : ℝ) (inside : time ∈ Icc 0 horizon) :
      HasDerivAt curve (deriv curve time) time ∧ ‖deriv curve time‖ ≤ bound := by
    obtain ⟨velocity, derivative, estimate⟩ := actual time inside
    rw [derivative.deriv]
    exact ⟨derivative, estimate⟩
  simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_right_le_segment continuous
    (fun time inside => (derivatives time ⟨inside.1, inside.2.le⟩).1.hasDerivWithinAt)
    (fun time inside => (derivatives time ⟨inside.1, inside.2.le⟩).2)

end EulerNonuniqueness.General
