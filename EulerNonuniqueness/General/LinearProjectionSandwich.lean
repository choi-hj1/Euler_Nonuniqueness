import EulerNonuniqueness.General.InvolutionProjection

namespace EulerNonuniqueness.General

noncomputable section

variable {Domain Middle : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]

theorem negativeInvolutionProjection_sandwich
    (reconstruct : Middle →L[ℝ] Domain) (coordinates : Domain →L[ℝ] Middle)
    (inverse : reconstruct.comp coordinates = ContinuousLinearMap.id ℝ Domain)
    (involution : Middle →L[ℝ] Middle) :
    reconstruct.comp ((negativeInvolutionProjection involution).comp coordinates) =
      negativeInvolutionProjection (reconstruct.comp (involution.comp coordinates)) := by
  have inverseValue (value : Domain) : reconstruct (coordinates value) = value :=
    congrArg (fun linear : Domain →L[ℝ] Domain => linear value) inverse
  ext value
  simp only [negativeInvolutionProjection, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    map_smul, map_sub, inverseValue]

end

end EulerNonuniqueness.General
