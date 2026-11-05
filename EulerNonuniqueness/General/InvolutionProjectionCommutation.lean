import EulerNonuniqueness.General.InvolutionProjection

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem negativeInvolutionProjection_commutes (involution operator : Space →L[ℝ] Space)
    (commutes : involution.comp operator = operator.comp involution) :
    (negativeInvolutionProjection involution).comp operator =
      operator.comp (negativeInvolutionProjection involution) := by
  have pointwise (value : Space) : involution (operator value) = operator (involution value) :=
    congrArg (fun current : Space →L[ℝ] Space => current value) commutes
  ext value
  simp only [negativeInvolutionProjection, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_smul, map_sub, pointwise]

end

end EulerNonuniqueness.General
