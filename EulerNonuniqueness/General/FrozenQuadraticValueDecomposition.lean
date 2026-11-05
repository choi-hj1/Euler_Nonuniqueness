import EulerNonuniqueness.General.MovingQuadraticForcingSplit

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem frozenProjectedQuadraticVelocity_self_decomposition
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (state remainder velocity : Space) (coefficient : BilinearEnd Space)
    (projectedEquation : projection (field state) = generator (projection state) +
      quadratic state (projection state) (projection state) + projection remainder)
    (velocityEquation : velocity = quadratic state (projection state) (projection state) + projection remainder)
    (coefficientEquation : coefficient = correction state) :
    frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 =
      generator (quadraticCoordinate (correction state) 1 (projection state)) +
        (projection remainder - (coefficient velocity (projection state) + coefficient (projection state) velocity)) := by
  have cancellation : generator (projection state) +
      quadratic state (projection state) (projection state) + projection remainder -
      generator (projection state) - quadratic state (projection state) (projection state) =
      projection remainder := by abel
  simp only [frozenProjectedQuadraticVelocity, map_zero, add_zero, projectedEquation, cancellation,
    velocityEquation, coefficientEquation]

end

end EulerNonuniqueness.General
