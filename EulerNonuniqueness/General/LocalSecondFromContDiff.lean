import EulerNonuniqueness.General.LocalSecondRegularity

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem localSecondDerivativeNear_of_contDiffAt_three
    {function : Domain → Target} {point : Domain} (smooth : ContDiffAt ℝ 3 function point) :
    HasLipschitzSecondDerivativeNear function point := by
  refine ⟨hasLipschitzDerivativeNear_of_contDiffAt_two (smooth.of_le (by decide)), ?_⟩
  exact hasLipschitzDerivativeNear_of_contDiffAt_two (smooth.fderiv_right (by decide))

end EulerNonuniqueness.General
