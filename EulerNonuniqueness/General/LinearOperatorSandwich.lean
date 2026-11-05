import Mathlib.Analysis.Calculus.Deriv.Mul

namespace EulerNonuniqueness.General

variable {Domain Middle : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Middle] [NormedSpace ℝ Middle]

theorem linearOperatorSandwich_hasDerivAt
    (reconstruct : Middle →L[ℝ] Domain) (coordinates : Domain →L[ℝ] Middle)
    {group : ℝ → Middle →L[ℝ] Middle} {derivative : Middle →L[ℝ] Middle} {time : ℝ}
    (actual : HasDerivAt group derivative time) :
    HasDerivAt (fun current => reconstruct.comp ((group current).comp coordinates))
      (reconstruct.comp (derivative.comp coordinates)) time := by
  have inner := actual.clm_comp (hasDerivAt_const time coordinates)
  have outer := (hasDerivAt_const time reconstruct).clm_comp inner
  simpa only [ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp, zero_add, add_zero] using outer

end EulerNonuniqueness.General
