import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem norm_sub_reference_le_of_eq_add {Space : Type*} [SeminormedAddCommGroup Space]
    {data base direction reference : Space} (value : data = base + direction) :
    ‖data - reference‖ ≤ ‖base - reference‖ + ‖direction‖ := by
  rw [value, show base + direction - reference = (base - reference) + direction by abel]
  exact norm_add_le _ _

theorem moving_slope_error_budget (frozen parameter main variation : ℝ)
    (frozenNonnegative : 0 ≤ frozen) (parameterNonnegative : 0 ≤ parameter)
    (mainNonnegative : 0 ≤ main) (variationNonnegative : 0 ≤ variation) :
    frozen * main + parameter * variation ≤
      (frozen + parameter + 1) * (main + variation) := by
  have leftover : 0 ≤ frozen * variation + parameter * main + main + variation := by positivity
  nlinarith only [leftover]

end EulerNonuniqueness.General
