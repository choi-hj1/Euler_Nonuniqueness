import EulerNonuniqueness.General.LocalUniformQuadraticRemainder

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem HasLipschitzDerivativeNear.exists_constraint_tangent_quadratic
    (function : Space → Target) (regular : HasLipschitzDerivativeNear function (0 : Space)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ base increment : Space,
      ‖base‖ + ‖increment‖ ≤ radius → function (base + increment) = function base →
      ‖fderiv ℝ function base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
  obtain ⟨radius, positive, constant, nonnegative, remainder⟩ := regular.exists_uniform_quadratic_remainder function
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro base increment inside sameValue
  simpa only [sameValue, sub_self, zero_sub, norm_neg] using remainder base increment inside

end

end EulerNonuniqueness.General
