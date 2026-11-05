import EulerNonuniqueness.General.MetricSlopeComparison

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem operator_weighted_split_increment_norm_le
    (operators : ℝ → Space →L[ℝ] Space) (curve main : ℝ → Space)
    {base later bound rate : ℝ} (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ time value, ‖operators time value‖ ≤ bound * ‖value‖)
    (initialEquality : curve base = main base)
    (increment : ‖curve later - curve base - (main later - main base)‖ ≤ rate * (later - base)) :
    ‖(operators later (curve later) - operators base (curve base)) -
      (operators later (main later) - operators base (main base))‖ ≤
        (bound * rate) * (later - base) := by
  have identity : (operators later (curve later) - operators base (curve base)) -
      (operators later (main later) - operators base (main base)) =
      operators later (curve later - curve base - (main later - main base)) := by
    rw [initialEquality]
    simp only [map_sub]
    abel
  rw [identity]
  exact (bounded later _).trans ((mul_le_mul_of_nonneg_left increment boundNonnegative).trans_eq (by ring))

end EulerNonuniqueness.General
