import Mathlib

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

def negativeInvolutionProjection (involution : Space →L[ℝ] Space) : Space →L[ℝ] Space :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ Space - involution)

theorem negativeInvolutionProjection_comp
    (involution : Space →L[ℝ] Space)
    (square : involution.comp involution = ContinuousLinearMap.id ℝ Space) :
    (negativeInvolutionProjection involution).comp involution = -negativeInvolutionProjection involution ∧
      involution.comp (negativeInvolutionProjection involution) = -negativeInvolutionProjection involution := by
  have squareValue (value : Space) : involution (involution value) = value :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value) square
  constructor <;> ext value <;>
    simp only [negativeInvolutionProjection, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.neg_apply, map_smul, map_sub, squareValue] <;> module

theorem negativeInvolutionProjection_idempotent
    (involution : Space →L[ℝ] Space)
    (square : involution.comp involution = ContinuousLinearMap.id ℝ Space) :
    (negativeInvolutionProjection involution).comp (negativeInvolutionProjection involution) =
      negativeInvolutionProjection involution := by
  have halfValue (value : Space) :
      involution (negativeInvolutionProjection involution value) = -negativeInvolutionProjection involution value :=
    congrArg (fun operator : Space →L[ℝ] Space => operator value)
      (negativeInvolutionProjection_comp involution square).2
  ext value
  change (1 / 2 : ℝ) • (negativeInvolutionProjection involution value -
      involution (negativeInvolutionProjection involution value)) = negativeInvolutionProjection involution value
  rw [halfValue]
  module

end

end EulerNonuniqueness.General
