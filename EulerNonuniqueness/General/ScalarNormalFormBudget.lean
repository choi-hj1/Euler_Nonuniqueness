import Mathlib.Tactic

namespace EulerNonuniqueness.General

theorem four_coefficient_normal_form_budget
    {groupBound selfCoefficient forcingCoefficient costSelf costForce selfSize forceSize : ℝ}
    (groupNonnegative : 0 ≤ groupBound) (selfNonnegative : 0 ≤ selfCoefficient)
    (forcingNonnegative : 0 ≤ forcingCoefficient) (costSelfNonnegative : 0 ≤ costSelf)
    (costForceNonnegative : 0 ≤ costForce) (selfSizeNonnegative : 0 ≤ selfSize)
    (forceNonnegative : 0 ≤ forceSize) :
    groupBound * (selfCoefficient * selfSize + forcingCoefficient * forceSize) +
        groupBound * (costSelf * selfSize + costForce * forceSize) ≤
      (groupBound * (selfCoefficient + forcingCoefficient + costSelf + costForce) + 1) * (selfSize + forceSize) := by
  apply sub_nonneg.mp
  have positive : 0 ≤ groupBound *
      (selfCoefficient * forceSize + forcingCoefficient * selfSize + costSelf * forceSize + costForce * selfSize) +
      selfSize + forceSize := by positivity
  convert positive using 1 <;> ring

theorem add_mul_lt_of_small_extra {mainSize groupBound cost extra threshold : ℝ}
    (small : groupBound * extra < threshold - (mainSize + groupBound * cost)) :
    mainSize + groupBound * (cost + extra) < threshold := by nlinarith

end EulerNonuniqueness.General
