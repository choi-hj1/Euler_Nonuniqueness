import EulerNonuniqueness.Section3.HolderQuotientJetBounds
import EulerNonuniqueness.Section3.ContourQuotientDerivative

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

def contourQuotientQuadratic (data increment : PeriodicC1HolderHalf) : PeriodicHolderHalf :=
  holderQuotientQuadratic data.val.2 increment.val.2

theorem contourQuotientDerivativeCLM_eq_holderLinear (data increment : PeriodicC1HolderHalf) :
    contourQuotientDerivativeCLM data increment = holderQuotientLinear data.val.2 increment.val.2 := rfl

theorem extendedHolderInverse_tangent_uniform_norm_bound (data : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖extendedHolderInverse data.val.2‖ ≤ contourTangentInverseConstant radius := by
  have equality : extendedHolderInverse data.val.2 =
      contourTangentInverse data (nearby.trans_lt small) := by
    rw [extendedHolderInverse_eq data.val.2
      (sub_pos.mpr ((nearby.trans_lt small).trans_le (min_le_left _ _)))
      (PeriodicC1HolderHalf.tangent_lower_bound data)]
    rfl
  rw [equality]
  exact contourTangentInverse_uniform_norm_bound data nonnegative small nearby

theorem contourQuotientQuadratic_norm_bound (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourQuotientQuadratic data increment‖ ≤
      (32 * (radius + 2) * contourTangentInverseConstant radius ^ 3 +
        8 * contourTangentInverseConstant radius ^ 2) * ‖increment‖ ^ 2 := by
  have inverse_bound := extendedHolderInverse_tangent_uniform_norm_bound data nonnegative small nearby
  have inverse_nonnegative := contourTangentInverseConstant_nonneg nonnegative small
  have tangent_bound := (PeriodicC1HolderHalf.tangent_norm_bound data).trans
    (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby)
  exact (holderQuotientQuadratic_norm_bound data.val.2 increment.val.2
    inverse_nonnegative inverse_bound).trans (by
      gcongr
      exact PeriodicC1HolderHalf.tangent_norm_bound increment)

theorem contourQuotient_cubic_remainder_norm (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius)
    (next_nearby : ‖data + increment - standardCircleBanach‖ ≤ radius)
    (increment_small : ‖increment‖ ≤ (1 - radius) / 2) (increment_bound : ‖increment‖ ≤ 1) :
    ‖extendedContourTangentQuotient (data + increment) - extendedContourTangentQuotient data -
      contourQuotientDerivativeCLM data increment - contourQuotientQuadratic data increment‖ ≤
      (128 * (radius + 3) * contourTangentInverseConstant radius ^ 4 +
        32 * contourTangentInverseConstant radius ^ 3) * ‖increment‖ ^ 3 := by
  have lower_positive : 0 < 1 - radius := sub_pos.mpr (small.trans_le (min_le_left _ _))
  have separated : ∀ label, 1 - radius ≤ ‖data.val.2.val.1 label‖ := fun label =>
    (sub_le_sub_left nearby 1).trans (PeriodicC1HolderHalf.tangent_lower_bound data label)
  have inverse_nonnegative := contourTangentInverseConstant_nonneg nonnegative small
  have first_bound := extendedHolderInverse_tangent_uniform_norm_bound data nonnegative small nearby
  have second_bound := extendedHolderInverse_tangent_uniform_norm_bound
    (data + increment) nonnegative small next_nearby
  have tangent_increment := PeriodicC1HolderHalf.tangent_norm_bound increment
  have tangent_data := (PeriodicC1HolderHalf.tangent_norm_bound data).trans
    (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby)
  rw [contourQuotientDerivativeCLM_eq_holderLinear]
  change ‖holderConjugateQuotient (data.val.2 + increment.val.2) -
      holderConjugateQuotient data.val.2 - holderQuotientLinear data.val.2 increment.val.2 -
      holderQuotientQuadratic data.val.2 increment.val.2‖ ≤ _
  apply (holderQuotient_cubic_remainder_norm data.val.2 increment.val.2 lower_positive separated
    (tangent_increment.trans increment_small) inverse_nonnegative first_bound second_bound
    (tangent_increment.trans increment_bound)).trans
  calc
    _ ≤ (128 * ((radius + 2) + 1) * contourTangentInverseConstant radius ^ 4 +
        32 * contourTangentInverseConstant radius ^ 3) * ‖increment‖ ^ 3 := by gcongr
    _ = _ := by ring

end

end EulerNonuniqueness.Paper
