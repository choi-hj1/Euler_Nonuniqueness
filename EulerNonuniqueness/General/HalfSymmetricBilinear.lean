import Mathlib

namespace EulerNonuniqueness.General

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space]

theorem eq_half_add_half_of_eq {first second : Space} (equal : first = second) :
    first = (1 / 2 : ℝ) • first + (1 / 2 : ℝ) • second := by
  rw [← equal, ← add_smul]
  norm_num

end EulerNonuniqueness.General
