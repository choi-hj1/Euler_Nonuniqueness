import EulerNonuniqueness.Section3.C1InverseAnalytic
import EulerNonuniqueness.General.LocalC1LipschitzBounds

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

theorem c1_near_one_separated (data : PeriodicC1HolderHalf)
    (small : ‖data - c1Constant 1‖ ≤ 1 / 2) (label : ℝ) : 1 / 2 ≤ ‖data.val.1 label‖ := by
  have point := PeriodicC1HolderHalf.value_bound (data - c1Constant 1) label
  change ‖data.val.1 label - 1‖ ≤ ‖data - c1Constant 1‖ at point
  have triangle := norm_sub_le (data.val.1 label) (data.val.1 label - 1)
  have identity : data.val.1 label - (data.val.1 label - 1) = 1 := by ring
  rw [identity, norm_one] at triangle
  linarith

theorem extendedC1Inverse_exists_uniform_ball :
    ∃ radius > 0, radius ≤ 1 / 2 ∧ ∃ constant ≥ 1,
      (∀ point : PeriodicC1HolderHalf, ‖point - c1Constant 1‖ ≤ radius →
        DifferentiableAt ℝ extendedC1Inverse point ∧ ‖fderiv ℝ extendedC1Inverse point‖ ≤ constant) ∧
      (∀ first final : PeriodicC1HolderHalf,
        ‖first - c1Constant 1‖ ≤ radius → ‖final - c1Constant 1‖ ≤ radius →
        ‖extendedC1Inverse first - extendedC1Inverse final‖ ≤ constant * ‖first - final‖) ∧
      ∀ first final : PeriodicC1HolderHalf,
        ‖first - c1Constant 1‖ ≤ radius → ‖final - c1Constant 1‖ ≤ radius →
        ‖fderiv ℝ extendedC1Inverse first - fderiv ℝ extendedC1Inverse final‖ ≤ constant * ‖first - final‖ := by
  have regular := extendedC1Inverse_hasLipschitzDerivativeNear_one
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne,
    differentiable, derivativeBound, derivativeDifference⟩ := regular.exists_uniform_derivative_ball
  obtain ⟨valueRadius, valuePositive, valueConstant, valueOne, valueDifference⟩ :=
    regular.lipschitzNear.exists_centered_closedBall_difference_bound
  let radius := min derivativeRadius (min valueRadius (1 / 2))
  let constant := derivativeConstant + valueConstant
  have derivativeLe : derivativeConstant ≤ constant := by dsimp [constant]; linarith
  have valueLe : valueConstant ≤ constant := by dsimp [constant]; linarith
  have derivativeRadiusLe : radius ≤ derivativeRadius := min_le_left _ _
  have valueRadiusLe : radius ≤ valueRadius := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨radius, by dsimp [radius]; positivity, (min_le_right _ _).trans (min_le_right _ _),
    constant, by dsimp [constant]; linarith, ?_, ?_, ?_⟩
  · intro point inside
    exact ⟨differentiable point (inside.trans derivativeRadiusLe),
      (derivativeBound point (inside.trans derivativeRadiusLe)).trans derivativeLe⟩
  · intro first final firstInside finalInside
    exact (valueDifference first final (firstInside.trans valueRadiusLe) (finalInside.trans valueRadiusLe)).trans
      (mul_le_mul_of_nonneg_right valueLe (norm_nonneg _))
  · intro first final firstInside finalInside
    exact (derivativeDifference first final (firstInside.trans derivativeRadiusLe) (finalInside.trans derivativeRadiusLe)).trans
      (mul_le_mul_of_nonneg_right derivativeLe (norm_nonneg _))

end EulerNonuniqueness.Paper
