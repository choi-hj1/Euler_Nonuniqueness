import EulerNonuniqueness.General.RealPhaseLiftUniqueness
import EulerNonuniqueness.Section4.ReferenceStatement

noncomputable section

open Set

namespace EulerNonuniqueness.Paper

theorem ReferencePhaseLift.eqOn_of_nonzero {count : ℕ} {motion : PatchMotion count}
    {phase : Fin count → ℝ} {first second : ℝ → Fin count → ℝ}
    (firstLift : ReferencePhaseLift motion phase first) (secondLift : ReferencePhaseLift motion phase second)
    (nonzero : ∀ time ∈ Icc (0 : ℝ) 2, ∀ index, positiveHalfDiagonal motion time index ≠ 0) :
    ∀ index, EqOn (fun time => first time index) (fun time => second time index) (Icc (0 : ℝ) 2) := by
  intro index
  exact General.real_phase_lift_eqOn_Icc (by norm_num : (0 : ℝ) ≤ 2)
    (firstLift index).1 (secondLift index).1 (fun time member => nonzero time member index)
    (firstLift index).2.2 (secondLift index).2.2 ((firstLift index).2.1.trans (secondLift index).2.1.symm)

end EulerNonuniqueness.Paper
