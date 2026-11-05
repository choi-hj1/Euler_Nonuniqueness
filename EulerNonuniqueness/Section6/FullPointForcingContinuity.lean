import EulerNonuniqueness.Section6.PointShapeForcingContinuity

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem fourPointTotalOddForcing_continuousOn (coefficient : ℝ)
    {times : Set ℝ} {positions forcing : ℝ → FourPointConfiguration}
    (positionsContinuous : ContinuousOn positions times)
    (forcingContinuous : ContinuousOn forcing times)
    (noncollision : ∀ time ∈ times, FourPointNoncollision (positions time))
    (positiveNonzero : ∀ time ∈ times, (fourPointOddPart (positions time)).1 ≠ 0)
    (negativeNonzero : ∀ time ∈ times, (fourPointOddPart (positions time)).2 ≠ 0)
    (squaresNonzero : ∀ time ∈ times,
      star (fourPointOddPart (positions time)).1 ^ 2 -
        star (fourPointOddPart (positions time)).2 ^ 2 ≠ 0) :
    ContinuousOn (fun time => fourPointTotalOddForcing coefficient (positions time) (forcing time)) times := by
  have oddContinuous : Continuous (fourPointOddPart : FourPointConfiguration → ℂ × ℂ) := by
    unfold fourPointOddPart
    fun_prop
  have odd := oddContinuous.comp_continuousOn positionsContinuous
  have field : ContinuousOn (fun time => fourPointField coefficient (positions time)) times := by
    intro time member
    exact ContinuousAt.comp_continuousWithinAt (f := positions)
      (fourPointField_contDiffAt coefficient (noncollision time member)).continuousAt
      (positionsContinuous time member)
  have velocities := pointVelocities_continuousOn coefficient odd.fst odd.snd
    positiveNonzero negativeNonzero squaresNonzero
  exact ((oddContinuous.comp_continuousOn field).sub (velocities.1.prodMk velocities.2)).add
    (oddContinuous.comp_continuousOn forcingContinuous)

end EulerNonuniqueness.Section6
