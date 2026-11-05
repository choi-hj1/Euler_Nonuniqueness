import Mathlib.Analysis.Normed.Group.Basic

namespace EulerNonuniqueness.General

theorem norm_four_add_sub_le {Space : Type*} [SeminormedAddCommGroup Space]
    (self leading higher tail transport : Space) :
    ‖self + leading + higher + tail - transport‖ ≤ ‖self‖ + ‖leading‖ + ‖higher‖ + ‖tail‖ + ‖transport‖ := by
  exact (norm_sub_le _ _).trans (add_le_add_right
    ((norm_add_le _ _).trans (add_le_add_right
      ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)) _)

end EulerNonuniqueness.General
