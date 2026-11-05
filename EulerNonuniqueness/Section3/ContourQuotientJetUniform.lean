import EulerNonuniqueness.Section3.ContourQuotientCubicTaylor

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

def contourQuotientQuadraticBound (radius : ℝ) : ℝ :=
  32 * (radius + 2) * contourTangentInverseConstant radius ^ 3 +
    8 * contourTangentInverseConstant radius ^ 2

def contourQuotientCubicBound (radius : ℝ) : ℝ :=
  128 * (radius + 3) * contourTangentInverseConstant radius ^ 4 +
    32 * contourTangentInverseConstant radius ^ 3

theorem contourQuotientQuadraticBound_nonnegative {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourQuotientQuadraticBound radius := by
  have inverse_nonnegative := contourTangentInverseConstant_nonneg nonnegative small
  unfold contourQuotientQuadraticBound
  positivity

theorem contourQuotientCubicBound_nonnegative {radius : ℝ} (nonnegative : 0 ≤ radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : 0 ≤ contourQuotientCubicBound radius := by
  have inverse_nonnegative := contourTangentInverseConstant_nonneg nonnegative small
  unfold contourQuotientCubicBound
  positivity

theorem contourQuotientDerivative_uniform_norm_bound (data increment : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖contourQuotientDerivativeCLM data increment‖ ≤
      contourTangentQuotientLipschitzConstant radius * ‖increment‖ := by
  rw [contourQuotientDerivativeCLM_eq_holderLinear]
  have inverse_nonnegative := contourTangentInverseConstant_nonneg nonnegative small
  have inverse_bound := extendedHolderInverse_tangent_uniform_norm_bound data nonnegative small nearby
  have tangent_data := (PeriodicC1HolderHalf.tangent_norm_bound data).trans
    (PeriodicC1HolderHalf.norm_le_radius_add_two data nearby)
  have bound := holderQuotientLinear_norm_bound data.val.2 increment.val.2 inverse_nonnegative inverse_bound
  apply bound.trans
  unfold contourTangentQuotientLipschitzConstant
  calc
    _ ≤ (8 * (radius + 2) * contourTangentInverseConstant radius ^ 2 +
        2 * contourTangentInverseConstant radius) * ‖increment‖ := by
      gcongr
      exact PeriodicC1HolderHalf.tangent_norm_bound increment
    _ = _ := by ring

theorem extendedContourTangentQuotient_uniform_norm_bound (data : PeriodicC1HolderHalf)
    {radius : ℝ} (nonnegative : 0 ≤ radius) (small : radius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ radius) :
    ‖extendedContourTangentQuotient data‖ ≤ contourTangentQuotientConstant radius := by
  rw [extendedContourTangentQuotient_eq data (nearby.trans_lt small)]
  exact contourTangentQuotient_uniform_norm_bound data nonnegative small nearby

end

end EulerNonuniqueness.Paper
