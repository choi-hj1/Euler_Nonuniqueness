import EulerNonuniqueness.Section3.HolderQuotientCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem holderInverseDerivative_norm_bound (data increment : PeriodicHolderHalf)
    {bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (inverse_bound : ‖extendedHolderInverse data‖ ≤ bound) :
    ‖holderInverseDerivativeCLM data increment‖ ≤ (4 * bound ^ 2) * ‖increment‖ := by
  change ‖-holderProduct (extendedHolderInverse data)
    (holderProduct increment (extendedHolderInverse data))‖ ≤ _
  rw [norm_neg]
  calc
    _ ≤ 2 * ‖extendedHolderInverse data‖ *
        (2 * ‖increment‖ * ‖extendedHolderInverse data‖) := by
      apply (holderProduct_norm_bound _ _).trans
      gcongr
      exact holderProduct_norm_bound _ _
    _ ≤ 2 * bound * (2 * ‖increment‖ * bound) := by gcongr
    _ = _ := by ring

theorem holderQuotientLinear_norm_bound (data increment : PeriodicHolderHalf)
    {bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (inverse_bound : ‖extendedHolderInverse data‖ ≤ bound) :
    ‖holderQuotientLinear data increment‖ ≤
      (8 * ‖data‖ * bound ^ 2 + 2 * bound) * ‖increment‖ := by
  have first_bound := holderInverseDerivative_norm_bound data increment bound_nonnegative inverse_bound
  have conjugate_data := holderConjugate_norm_bound data
  have conjugate_increment := holderConjugate_norm_bound increment
  unfold holderQuotientLinear
  apply (norm_add_le _ _).trans
  apply (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)).trans
  calc
    _ ≤ 2 * ‖data‖ * ((4 * bound ^ 2) * ‖increment‖) + 2 * ‖increment‖ * bound := by gcongr
    _ = _ := by ring

theorem holderQuotientQuadratic_norm_bound (data increment : PeriodicHolderHalf)
    {bound : ℝ} (bound_nonnegative : 0 ≤ bound)
    (inverse_bound : ‖extendedHolderInverse data‖ ≤ bound) :
    ‖holderQuotientQuadratic data increment‖ ≤
      (32 * ‖data‖ * bound ^ 3 + 8 * bound ^ 2) * ‖increment‖ ^ 2 := by
  have linear_bound := holderInverseDerivative_norm_bound data increment bound_nonnegative inverse_bound
  have quadratic_bound := holderInverseQuadratic_norm_bound data increment bound_nonnegative inverse_bound
  have conjugate_data := holderConjugate_norm_bound data
  have conjugate_increment := holderConjugate_norm_bound increment
  unfold holderQuotientQuadratic
  apply (norm_add_le _ _).trans
  apply (add_le_add (holderProduct_norm_bound _ _) (holderProduct_norm_bound _ _)).trans
  calc
    _ ≤ 2 * ‖data‖ * ((16 * bound ^ 3) * ‖increment‖ ^ 2) +
        2 * ‖increment‖ * ((4 * bound ^ 2) * ‖increment‖) := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
