import EulerNonuniqueness.General.MovingQuadraticForcingSplit

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

def movingQuadraticSelfRemainder (projection neutral : Space →L[ℝ] Space)
    (quadratic correction bilinear : Space → BilinearEnd Space)
    (differential : Space →L[ℝ] BilinearEnd Space) (state remainder : Space) : Space :=
  let value := projection state
  projection remainder -
    (correction state (quadratic state value value + projection remainder) value +
      correction state value (quadratic state value value + projection remainder)) -
    differential (neutral (bilinear state value value) + neutral remainder) value value

theorem movingQuadraticSelfVelocity_eq_generator_add_remainder
    (projection neutral generator : Space →L[ℝ] Space)
    (quadratic correction bilinear : Space → BilinearEnd Space) (field : Space → Space)
    (differential : Space →L[ℝ] BilinearEnd Space) (state remainder : Space)
    (projectedEquation : projection (field state) = generator (projection state) +
      quadratic state (projection state) (projection state) + projection remainder)
    (neutralEquation : neutral (field state) =
      neutral (bilinear state (projection state) (projection state)) + neutral remainder) :
    frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 -
        differential (neutral (field state)) (projection state) (projection state) =
      generator (quadraticCoordinate (correction state) 1 (projection state)) +
        movingQuadraticSelfRemainder projection neutral quadratic correction bilinear differential state remainder := by
  have cancellation : generator (projection state) +
      quadratic state (projection state) (projection state) + projection remainder -
      generator (projection state) - quadratic state (projection state) (projection state) =
      projection remainder := by abel
  simp only [frozenProjectedQuadraticVelocity, movingQuadraticSelfRemainder, map_zero, add_zero,
    projectedEquation, neutralEquation, cancellation]
  abel

end

end EulerNonuniqueness.General
