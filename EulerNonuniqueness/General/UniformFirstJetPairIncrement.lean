import EulerNonuniqueness.General.RelativeLinearIncrement

noncomputable section

open Metric

namespace EulerNonuniqueness.General

variable {Domain Target : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem norm_pair_increment_le_of_uniform_firstJet
    (function : Domain → Target) (derivative : Domain → Domain →L[ℝ] Target)
    {radius bound : ℝ} (nonnegative : 0 ≤ bound)
    (actual : ∀ point ∈ closedBall (0 : Domain) radius, HasFDerivAt function (derivative point) point)
    (derivativeBound : ∀ point ∈ closedBall (0 : Domain) radius, ‖derivative point‖ ≤ bound)
    (derivativeDifference : ∀ first ∈ closedBall (0 : Domain) radius,
      ∀ second ∈ closedBall (0 : Domain) radius, ‖derivative first - derivative second‖ ≤ bound * ‖first - second‖)
    (first second initial final : Domain)
    (firstInside : ‖first‖ + (‖initial‖ + ‖final‖) ≤ radius)
    (secondInside : ‖second‖ + (‖initial‖ + ‖final‖) ≤ radius) :
    ‖(function (first + initial) - function first) -
      (function (second + final) - function second)‖ ≤
      bound * (‖initial - final‖ + ‖first - second‖ * ‖final‖) := by
  have functionLip : LipschitzOnWith ⟨bound, nonnegative⟩ function (closedBall (0 : Domain) radius) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := derivative) (fun point member => (actual point member).hasFDerivWithinAt) _ (convex_closedBall _ _)
    intro point member
    change ‖derivative point‖ ≤ bound
    exact derivativeBound point member
  have derivativeLip : LipschitzOnWith ⟨bound, nonnegative⟩ derivative (closedBall (0 : Domain) radius) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    exact derivativeDifference
  have shiftedMember (increment : Domain) (bounded : ‖increment‖ ≤ ‖initial‖ + ‖final‖) :
      first + increment ∈ closedBall (0 : Domain) radius :=
    mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans ((add_le_add_left bounded _).trans firstInside))
  have firstEstimate := functionLip.norm_sub_le
    (shiftedMember initial (le_add_of_nonneg_right (norm_nonneg _)))
    (shiftedMember final (le_add_of_nonneg_left (norm_nonneg _)))
  have firstControl : ‖(function (first + initial) - function first) -
      (function (first + final) - function first)‖ ≤ bound * ‖initial - final‖ := by
    simpa only [sub_sub_sub_cancel_right, add_sub_add_left_eq_sub, NNReal.coe_mk] using firstEstimate
  have baseControl := norm_increment_base_difference_of_lipschitz_derivative function derivative
    ⟨bound, nonnegative⟩ actual derivativeLip first second final
    (by linarith [norm_nonneg initial]) (by linarith [norm_nonneg initial])
  simp only [NNReal.coe_mk] at baseControl
  exact ((norm_sub_le_norm_sub_add_norm_sub
    (function (first + initial) - function first) (function (first + final) - function first)
    (function (second + final) - function second)).trans
      (add_le_add firstControl baseControl)).trans_eq (by ring)

end EulerNonuniqueness.General
