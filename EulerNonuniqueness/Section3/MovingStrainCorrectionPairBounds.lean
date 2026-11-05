import EulerNonuniqueness.Section3.MovingStrainAffineCoefficient
import EulerNonuniqueness.Section3.MovingStrainRealBaseBounds
import EulerNonuniqueness.General.AffineResidualRelativeRemainder

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] independentRealificationC1Group forcingModeC1RealSpace
  forcingModeC1ComplexModule forcingModeC1ComplexSpace
  secondIdentityOperatorGroup secondIdentityOperatorModule secondIdentityOperatorSpace

theorem movingStrainRealCorrectionCLM_sub_coefficient (base : PeriodicC1HolderHalf) (initial final : ℂ) :
    movingStrainRealCorrectionCLM base initial - movingStrainRealCorrectionCLM base final =
      movingStrainRealCorrectionCLM base (initial - final) := by
  have mapped := (movingStrainCorrectionCoefficient base).map_sub initial final
  simpa only [movingStrainCorrectionCoefficient_apply] using mapped.symm

theorem movingStrainRealCorrectionCLM_exists_pair_base_bounds :
    ∃ radius > 0, ∃ constant ≥ 0,
      (∀ base : PeriodicC1HolderHalf, ‖base - standardCircleBanach‖ ≤ radius → ∀ coefficient : ℂ,
        ‖movingStrainRealCorrectionCLM base coefficient‖ ≤ constant * ‖coefficient‖) ∧
      ∀ first final : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ∀ initialCoefficient finalCoefficient : ℂ,
      ‖movingStrainRealCorrectionCLM first initialCoefficient - movingStrainRealCorrectionCLM final finalCoefficient‖ ≤
        constant * (‖initialCoefficient‖ * ‖first - final‖ + ‖initialCoefficient - finalCoefficient‖) := by
  obtain ⟨radius, positive, constant, one, absolute, difference⟩ :=
    movingStrainRealCorrectionCLM_exists_uniform_base_bounds
  refine ⟨radius, positive, constant, le_trans (by norm_num) one, absolute, ?_⟩
  intro first final firstInside finalInside initialCoefficient finalCoefficient
  have base := difference first final firstInside finalInside initialCoefficient
  have coefficient : ‖movingStrainRealCorrectionCLM final initialCoefficient -
      movingStrainRealCorrectionCLM final finalCoefficient‖ ≤ constant * ‖initialCoefficient - finalCoefficient‖ := by
    rw [movingStrainRealCorrectionCLM_sub_coefficient]
    with_reducible_and_instances
      exact absolute final finalInside (initialCoefficient - finalCoefficient)
  have triangle := norm_sub_le_norm_sub_add_norm_sub
    (movingStrainRealCorrectionCLM first initialCoefficient)
    (movingStrainRealCorrectionCLM final initialCoefficient)
    (movingStrainRealCorrectionCLM final finalCoefficient)
  with_reducible_and_instances
    exact (le_trans triangle (add_le_add base coefficient)).trans_eq (by ring)

theorem movingStrainRealCorrectionCLM_exists_pair_apply_bounds :
    ∃ radius > 0, ∃ constant ≥ 0,
      ∀ first final : PeriodicC1HolderHalf,
      ‖first - standardCircleBanach‖ ≤ radius → ‖final - standardCircleBanach‖ ≤ radius →
      ∀ initialCoefficient finalCoefficient : ℂ, ∀ initialForce finalForce : PeriodicC1HolderHalf,
      ‖movingStrainRealCorrectionCLM first initialCoefficient initialForce -
        movingStrainRealCorrectionCLM final finalCoefficient finalForce‖ ≤
      constant * (‖initialCoefficient‖ * ‖initialForce - finalForce‖ +
        (‖initialCoefficient‖ * ‖first - final‖ + ‖initialCoefficient - finalCoefficient‖) * ‖finalForce‖) := by
  obtain ⟨radius, positive, constant, nonnegative, absolute, difference⟩ :=
    movingStrainRealCorrectionCLM_exists_pair_base_bounds
  refine ⟨radius, positive, constant, nonnegative, ?_⟩
  intro first final firstInside finalInside initialCoefficient finalCoefficient initialForce finalForce
  have firstBound := absolute first firstInside initialCoefficient
  have pairBound := difference first final firstInside finalInside initialCoefficient finalCoefficient
  let initialOperator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    movingStrainRealCorrectionCLM first initialCoefficient
  let finalOperator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    movingStrainRealCorrectionCLM final finalCoefficient
  have vector : ‖initialOperator initialForce - finalOperator finalForce‖ ≤
      ‖initialOperator‖ * ‖initialForce - finalForce‖ + ‖initialOperator - finalOperator‖ * ‖finalForce‖ := by
    with_reducible_and_instances
      exact EulerNonuniqueness.General.norm_operator_apply_difference_le initialOperator finalOperator initialForce finalForce
  have sums := add_le_add (mul_le_mul_of_nonneg_right firstBound (norm_nonneg (initialForce - finalForce)))
    (mul_le_mul_of_nonneg_right pairBound (norm_nonneg finalForce))
  with_reducible_and_instances
    exact (le_trans vector sums).trans_eq (by ring)

end EulerNonuniqueness.Paper
