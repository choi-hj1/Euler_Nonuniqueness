import EulerNonuniqueness.General.UniformQuadraticFirstJetLipschitz
import EulerNonuniqueness.General.RelativeLinearIncrement

noncomputable section

open Metric

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

theorem relative_increment_of_uniform_first_jet
    (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    {radius constant : ℝ} (positive : 0 < radius) (nonnegative : 0 ≤ constant)
    (linearBound : ∀ point, ‖point‖ ≤ radius → ‖linear point‖ ≤ constant)
    (taylor : ∀ point increment, ‖point‖ + ‖increment‖ ≤ radius →
      ‖linearJetTaylorError function linear point increment‖ ≤ constant * ‖increment‖ ^ 2)
    (actual : ∀ point, ‖point‖ < radius → HasFDerivAt function (linear point) point)
    (first second initial final : Domain)
    (firstInside : ‖first‖ + (‖initial‖ + ‖final‖) ≤ radius / 8)
    (secondInside : ‖second‖ + (‖initial‖ + ‖final‖) ≤ radius / 8) :
    ‖(function (first + initial) - function first) - (function (second + final) - function second)‖ ≤
      6 * constant * (‖initial - final‖ + ‖first - second‖ * ‖final‖) := by
  have innerLe : radius / 8 ≤ radius := by linarith
  have innerLt : radius / 8 < radius := by linarith
  have actualInner (point : Domain) (member : point ∈ closedBall (0 : Domain) (radius / 8)) :
      HasFDerivAt function (linear point) point :=
    actual point ((mem_closedBall_zero_iff.mp member).trans_lt innerLt)
  have functionLip : LipschitzOnWith ⟨constant, nonnegative⟩ function
      (closedBall (0 : Domain) (radius / 8)) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun point member => (actualInner point member).hasFDerivWithinAt) _ (convex_closedBall _ _)
    intro point member
    exact_mod_cast linearBound point ((mem_closedBall_zero_iff.mp member).trans innerLe)
  have linearLip : LipschitzOnWith ⟨6 * constant, by positivity⟩ linear
      (closedBall (0 : Domain) (radius / 8)) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro left leftInside right rightInside
    have leftNorm := mem_closedBall_zero_iff.mp leftInside
    have rightNorm := mem_closedBall_zero_iff.mp rightInside
    have taylorSmall (point : Domain) (pointBound : ‖point‖ ≤ radius / 8)
        (increment : Domain) (incrementBound : ‖increment‖ ≤ radius / 2) :
        ‖linearJetTaylorError function linear point increment‖ ≤ constant * ‖increment‖ ^ 2 :=
      taylor point increment (by linarith)
    exact linear_operator_difference_le_of_uniform_quadratic function linear right left nonnegative
      (taylorSmall right rightNorm) (taylorSmall left leftNorm)
      (by have bound := norm_sub_le left right; linarith)
  have shiftedMember (increment : Domain) (bound : ‖increment‖ ≤ ‖initial‖ + ‖final‖) :
      first + increment ∈ closedBall (0 : Domain) (radius / 8) :=
    mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans ((add_le_add_left bound _).trans firstInside))
  have firstEstimate := functionLip.norm_sub_le
    (shiftedMember initial (le_add_of_nonneg_right (norm_nonneg _)))
    (shiftedMember final (le_add_of_nonneg_left (norm_nonneg _)))
  have initialEstimate : ‖(function (first + initial) - function first) -
      (function (first + final) - function first)‖ ≤ constant * ‖initial - final‖ := by
    simpa only [sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] using firstEstimate
  have baseEstimate := norm_increment_base_difference_of_lipschitz_derivative function linear
    ⟨6 * constant, by positivity⟩ actualInner linearLip first second final
    (by linarith [norm_nonneg initial]) (by linarith [norm_nonneg initial])
  simp only [NNReal.coe_mk] at baseEstimate
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (function (first + initial) - function first) (function (first + final) - function first)
    (function (second + final) - function second)
  apply (triangle.trans (add_le_add initialEstimate baseEstimate)).trans
  nlinarith [mul_nonneg nonnegative (norm_nonneg (initial - final))]

end EulerNonuniqueness.General
