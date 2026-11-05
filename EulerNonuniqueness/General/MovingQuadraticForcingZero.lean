import EulerNonuniqueness.General.MovingQuadraticForcingSplit

noncomputable section

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem movingProjectedQuadraticForcing_zero
    (projection neutral : Space →L[ℝ] Space) (correction : BilinearEnd Space)
    (differential : Space →L[ℝ] BilinearEnd Space) (state : Space) :
    projection 0 - (correction (projection 0) (projection state) +
      correction (projection state) (projection 0)) -
      differential (neutral 0) (projection state) (projection state) = 0 := by
  simp only [map_zero, ContinuousLinearMap.zero_apply, add_zero, sub_zero]

end EulerNonuniqueness.General
