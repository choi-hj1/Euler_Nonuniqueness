import EulerNonuniqueness.General.MovingQuadraticSelfDecomposition

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem movingQuadraticSelfRemainder_eq_three_values
    (projection neutral : Space →L[ℝ] Space)
    (quadratic correction bilinear : Space → BilinearEnd Space)
    (differential : Space →L[ℝ] BilinearEnd Space)
    (state remainder velocity neutralVelocity : Space)
    (velocityEquation : velocity = quadratic state (projection state) (projection state) + projection remainder)
    (neutralEquation : neutralVelocity =
      neutral (bilinear state (projection state) (projection state)) + neutral remainder)
    (parameterEquation : correction (neutral state) = correction state) :
    movingQuadraticSelfRemainder projection neutral quadratic correction bilinear differential state remainder =
      projection remainder -
        (correction (neutral state) velocity (projection state) +
          correction (neutral state) (projection state) velocity) -
        differential neutralVelocity (projection state) (projection state) := by
  simp only [movingQuadraticSelfRemainder, parameterEquation, velocityEquation, neutralEquation]

end

end EulerNonuniqueness.General
