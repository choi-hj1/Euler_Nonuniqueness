import EulerNonuniqueness.General.LipschitzDerivativeQuadraticRemainder

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.General

noncomputable section

variable {Space Target : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem norm_quadratic_taylor_remainder_base_difference
    (function : Space → Target) (first : Space → Space →L[ℝ] Target)
    (second : Space → Space →L[ℝ] Space →L[ℝ] Target)
    {radius : ℝ} (constant : NNReal)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt function (first value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt first (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Space) radius))
    (initial final increment : Space)
    (initialInside : ‖initial‖ + ‖increment‖ ≤ radius)
    (finalInside : ‖final‖ + ‖increment‖ ≤ radius) :
    ‖(function (initial + increment) - function initial - first initial increment) -
      (function (final + increment) - function final - first final increment)‖ ≤
      (constant : ℝ) * ‖initial - final‖ * ‖increment‖ ^ 2 := by
  have contained (base : Space) (baseInside : ‖base‖ + ‖increment‖ ≤ radius)
      (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      base + point ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le base point).trans
      ((add_le_add_left (mem_closedBall_zero_iff.mp member) ‖base‖).trans baseInside)
  let difference := fun point => function (initial + point) - function (final + point)
  let derivative := fun point => first (initial + point) - first (final + point)
  let differential := fun point => second (initial + point) - second (final + point)
  have firstActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt difference (derivative point) point := by
    have initialTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add initial
    have finalTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add final
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualFirst _ (contained initial initialInside point member)).comp point initialTranslation).sub
        ((actualFirst _ (contained final finalInside point member)).comp point finalTranslation)
  have secondActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt derivative (differential point) point := by
    have initialTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add initial
    have finalTranslation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add final
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualSecond _ (contained initial initialInside point member)).comp point initialTranslation).sub
        ((actualSecond _ (contained final finalInside point member)).comp point finalTranslation)
  have differentialBound (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      ‖differential point‖₊ ≤ constant * ‖initial - final‖₊ := by
    have bound := LipschitzOnWith.norm_sub_le (f := second) lipschitz
      (contained initial initialInside point member) (contained final finalInside point member)
    have equal : (initial + point) - (final + point) = initial - final := by abel
    rw [equal] at bound
    exact_mod_cast bound
  have derivativeLipschitz := Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (fun point member => (secondActual point member).hasFDerivWithinAt) differentialBound
    (convex_closedBall (0 : Space) ‖increment‖)
  have bound := norm_quadratic_remainder_of_lipschitz_derivative difference derivative
    (constant * ‖initial - final‖₊) firstActual derivativeLipschitz
    (0 : Space) increment (by simp)
  have identity : difference (0 + increment) - difference 0 - derivative 0 increment =
      (function (initial + increment) - function initial - first initial increment) -
        (function (final + increment) - function final - first final increment) := by
    simp only [difference, derivative, zero_add, add_zero, ContinuousLinearMap.sub_apply]
    abel
  simpa only [identity, NNReal.coe_mul, coe_nnnorm] using bound

end

end EulerNonuniqueness.General
