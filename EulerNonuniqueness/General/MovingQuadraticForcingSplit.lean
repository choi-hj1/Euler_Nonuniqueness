import EulerNonuniqueness.General.MovingProjectedQuadraticFamily

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] cubicCoefficientEndGroup cubicCoefficientEndSpace
  cubicCoefficientBilinearGroup cubicCoefficientBilinearSpace

theorem frozenProjectedQuadraticVelocity_forcing_split
    (projection generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (state forcing : Space) :
    frozenProjectedQuadraticVelocity projection generator quadratic correction field state forcing =
      frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 +
        (projection forcing - (correction state (projection forcing) (projection state) +
          correction state (projection state) (projection forcing))) := by
  simp only [frozenProjectedQuadraticVelocity, map_zero, add_zero, map_add, map_sub,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  abel

theorem movingProjectedQuadraticVelocity_forcing_split
    (projection neutral generator : Space →L[ℝ] Space)
    (quadratic correction : Space → BilinearEnd Space) (field : Space → Space)
    (differential : Space →L[ℝ] BilinearEnd Space) (state forcing : Space) :
    frozenProjectedQuadraticVelocity projection generator quadratic correction field state forcing -
        differential (neutral (field state + forcing)) (projection state) (projection state) =
      (frozenProjectedQuadraticVelocity projection generator quadratic correction field state 0 -
        differential (neutral (field state)) (projection state) (projection state)) +
      (projection forcing - (correction state (projection forcing) (projection state) +
        correction state (projection state) (projection forcing)) -
        differential (neutral forcing) (projection state) (projection state)) := by
  rw [frozenProjectedQuadraticVelocity_forcing_split]
  simp only [map_add, ContinuousLinearMap.add_apply]
  abel

end

end EulerNonuniqueness.General
