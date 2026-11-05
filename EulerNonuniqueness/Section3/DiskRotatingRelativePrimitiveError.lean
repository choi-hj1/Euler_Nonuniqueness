import EulerNonuniqueness.Section3.DiskRotatingDerivativeRelativeIncrement
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondIdentityC1Space secondIdentityC1ContinuousAdd
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace
  secondIdentityOperatorUniformAdd secondIdentityOperatorContinuousAdd
  secondIdentityBilinearGroup secondIdentityBilinearModule secondLipschitzBilinearSpace

local instance rotatingRelativePrimitiveC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

theorem diskRotatingGeneratorPrimitive_exists_scaled_relative_ball :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ initial final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖initial - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ‖final - standardCircleBanach‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ radius →
      ∀ initialPrimitive finalPrimitive : PeriodicC1HolderHalf, ∀ frequency : ℝ,
      ‖frequency • ((fderiv ℝ diskEulerRotatingField (initial + initialIncrement) -
          fderiv ℝ diskEulerRotatingField initial) initialPrimitive) -
        frequency • ((fderiv ℝ diskEulerRotatingField (final + finalIncrement) -
          fderiv ℝ diskEulerRotatingField final) finalPrimitive)‖ ≤
      constant * |frequency| *
        (‖initialIncrement‖ * ‖initialPrimitive - finalPrimitive‖ +
          (‖initialIncrement - finalIncrement‖ + ‖initial - final‖ * ‖finalIncrement‖) * ‖finalPrimitive‖) := by
  obtain ⟨radius, positive, constant, nonnegative, bound⟩ :=
    diskEulerRotatingField_derivative_exists_relative_increment_ball
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro initial final initialIncrement finalIncrement initialInside finalInside initialPrimitive finalPrimitive frequency
  have relative := bound initial final initialIncrement finalIncrement initialInside finalInside
  have singleInside : ‖initial - standardCircleBanach‖ + (‖initialIncrement‖ + ‖(0 : PeriodicC1HolderHalf)‖) ≤ radius := by
    simp only [norm_zero, add_zero]
    linarith [norm_nonneg finalIncrement]
  have absolute := bound initial initial initialIncrement 0 singleInside singleInside
  simp only [add_zero, sub_self, sub_zero, norm_zero, mul_zero, add_zero] at absolute
  let firstOperator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskEulerRotatingField (initial + initialIncrement) - fderiv ℝ diskEulerRotatingField initial
  let finalOperator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    fderiv ℝ diskEulerRotatingField (final + finalIncrement) - fderiv ℝ diskEulerRotatingField final
  have vector : ‖firstOperator initialPrimitive - finalOperator finalPrimitive‖ ≤
      ‖firstOperator‖ * ‖initialPrimitive - finalPrimitive‖ +
        ‖firstOperator - finalOperator‖ * ‖finalPrimitive‖ := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.norm_operator_apply_difference_le firstOperator finalOperator
        initialPrimitive finalPrimitive
  have estimate : ‖firstOperator initialPrimitive - finalOperator finalPrimitive‖ ≤ constant *
      (‖initialIncrement‖ * ‖initialPrimitive - finalPrimitive‖ +
        (‖initialIncrement - finalIncrement‖ + ‖initial - final‖ * ‖finalIncrement‖) * ‖finalPrimitive‖) := by
    have sums := add_le_add
      (mul_le_mul_of_nonneg_right absolute (norm_nonneg (initialPrimitive - finalPrimitive)))
      (mul_le_mul_of_nonneg_right relative (norm_nonneg finalPrimitive))
    with_reducible_and_instances
      exact (le_trans vector sums).trans_eq (by ring)
  rw [← smul_sub, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left estimate (abs_nonneg frequency)).trans_eq (by ring)

end EulerNonuniqueness.Paper
