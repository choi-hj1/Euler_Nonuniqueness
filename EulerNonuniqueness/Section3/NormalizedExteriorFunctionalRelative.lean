import EulerNonuniqueness.Section3.NormalizedExteriorFunctionalUniform
import EulerNonuniqueness.General.RelativeLinearIncrement

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace

theorem normalizedExteriorFunctional_exists_relative_increment :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ∀ first final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖first‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 3 →
      ‖final‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 3 →
        ‖(normalizedExteriorFunctional parameter power (first + initialIncrement) -
            normalizedExteriorFunctional parameter power first) -
          (normalizedExteriorFunctional parameter power (final + finalIncrement) -
            normalizedExteriorFunctional parameter power final)‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ *
            (‖initialIncrement - finalIncrement‖ + ‖first - final‖ * ‖finalIncrement‖) := by
  obtain ⟨parameterRadius, positive, constant, one, bounds⟩ :=
    normalizedExteriorFunctional_exists_uniform_firstJet
  refine ⟨parameterRadius, positive, constant, one, ?_⟩
  intro parameter parameterSmall power first final initialIncrement finalIncrement firstInside finalInside
  have control := bounds parameter parameterSmall power
  let weight := constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖
  have weightNonnegative : 0 ≤ weight := by dsimp only [weight]; positivity
  have actual (point : PeriodicC1HolderHalf) (member : point ∈ closedBall (0 : PeriodicC1HolderHalf) 3) :
      HasFDerivAt (normalizedExteriorFunctional parameter power)
        (normalizedExteriorFunctionalDerivative parameter power point) point :=
    (control.1 point (mem_closedBall_zero_iff.mp member)).1
  have functionLip : LipschitzOnWith ⟨weight, weightNonnegative⟩
      (normalizedExteriorFunctional parameter power) (closedBall (0 : PeriodicC1HolderHalf) 3) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := normalizedExteriorFunctionalDerivative parameter power)
      (fun point member => (actual point member).hasFDerivWithinAt) _ (convex_closedBall _ _)
    intro point member
    change ‖normalizedExteriorFunctionalDerivative parameter power point‖ ≤ weight
    exact (control.1 point (mem_closedBall_zero_iff.mp member)).2
  have derivativeLip : LipschitzOnWith ⟨weight, weightNonnegative⟩
      (normalizedExteriorFunctionalDerivative parameter power) (closedBall (0 : PeriodicC1HolderHalf) 3) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro left leftInside right rightInside
    exact control.2 left right (mem_closedBall_zero_iff.mp leftInside) (mem_closedBall_zero_iff.mp rightInside)
  have shiftedMember (increment : PeriodicC1HolderHalf)
      (bounded : ‖increment‖ ≤ ‖initialIncrement‖ + ‖finalIncrement‖) :
      first + increment ∈ closedBall (0 : PeriodicC1HolderHalf) 3 :=
    mem_closedBall_zero_iff.mpr ((norm_add_le _ _).trans ((add_le_add_left bounded _).trans firstInside))
  have firstEstimate := functionLip.norm_sub_le
    (shiftedMember initialIncrement (le_add_of_nonneg_right (norm_nonneg _)))
    (shiftedMember finalIncrement (le_add_of_nonneg_left (norm_nonneg _)))
  have firstControl :
      ‖(normalizedExteriorFunctional parameter power (first + initialIncrement) -
          normalizedExteriorFunctional parameter power first) -
        (normalizedExteriorFunctional parameter power (first + finalIncrement) -
          normalizedExteriorFunctional parameter power first)‖ ≤ weight * ‖initialIncrement - finalIncrement‖ := by
    simpa only [sub_sub_sub_cancel_right, add_sub_add_left_eq_sub] using firstEstimate
  have baseControl := EulerNonuniqueness.General.norm_increment_base_difference_of_lipschitz_derivative
    (normalizedExteriorFunctional parameter power) (normalizedExteriorFunctionalDerivative parameter power)
    ⟨weight, weightNonnegative⟩ actual derivativeLip first final finalIncrement
    (by linarith [norm_nonneg initialIncrement]) (by linarith [norm_nonneg initialIncrement])
  simp only [NNReal.coe_mk] at baseControl
  exact ((norm_sub_le_norm_sub_add_norm_sub
    (normalizedExteriorFunctional parameter power (first + initialIncrement) - normalizedExteriorFunctional parameter power first)
    (normalizedExteriorFunctional parameter power (first + finalIncrement) - normalizedExteriorFunctional parameter power first)
    (normalizedExteriorFunctional parameter power (final + finalIncrement) - normalizedExteriorFunctional parameter power final)).trans
      (add_le_add firstControl baseControl)).trans_eq (by dsimp only [weight]; ring)

end EulerNonuniqueness.Paper
