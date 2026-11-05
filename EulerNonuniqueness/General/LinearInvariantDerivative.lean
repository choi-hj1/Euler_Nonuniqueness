import Mathlib

namespace EulerNonuniqueness.General

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem fderiv_comp_eq_of_linear_invariant
    (function : Space → Target) (linear : Space →L[ℝ] Space) (base : Space)
    (regularAtImage : DifferentiableAt ℝ function (linear base))
    (invariant : ∀ point, function (linear point) = function point) :
    (fderiv ℝ function (linear base)).comp linear = fderiv ℝ function base := by
  have composed := regularAtImage.hasFDerivAt.comp base (linear.hasFDerivAt (x := base))
  have identity : (fun point => function (linear point)) = function := funext invariant
  change HasFDerivAt (fun point => function (linear point)) ((fderiv ℝ function (linear base)).comp linear) base at composed
  rw [identity] at composed
  exact composed.fderiv.symm

end EulerNonuniqueness.General
