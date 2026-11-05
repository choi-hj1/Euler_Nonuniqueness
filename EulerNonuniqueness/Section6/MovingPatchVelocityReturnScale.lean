import EulerNonuniqueness.Section6.MovingPatchVelocityEndpoint

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem velocityCentroidCorrectionCenterEnvelope_normalized
    (comparison : MovingPatchSourceComparison) {frequency length separation : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2) :
    comparison.velocityCentroidCorrectionCenterEnvelope (separation * length) / (frequency * length) =
      (comparison.first.radius ^ 2 / length ^ 2) *
        (24 * separation⁻¹ ^ 4 * (‖comparison.displacementDifference‖ / length)) := by
  have radiusPositive := comparison.first.radius_positive
  have densityIdentity : |comparison.density| = 2 * frequency * length ^ 2 / comparison.first.radius ^ 2 :=
    (eq_div_iff (sq_pos_of_pos radiusPositive).ne').mpr mass
  unfold velocityCentroidCorrectionCenterEnvelope
  rw [densityIdentity]
  field_simp [frequencyPositive.ne', lengthPositive.ne', separationPositive.ne', radiusPositive.ne']
  <;> ring

theorem velocityCentroidCorrectionShapeEnvelope_normalized_le
    (comparison : MovingPatchSourceComparison) {frequency length separation constant : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (constantNonnegative : 0 ≤ constant)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2)
    (separated : separation * length ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖) :
    comparison.velocityCentroidCorrectionShapeEnvelope constant / (frequency * length) ≤
      (comparison.first.radius ^ 2 / length ^ 2) *
        (96 * constant / Real.pi * separation⁻¹ ^ 3 * comparison.spectralDifferenceBudget) := by
  let distance := ‖comparison.secondReceiver - comparison.second.center comparison.time‖
  have distancePositive : 0 < distance := lt_of_lt_of_le (mul_pos separationPositive lengthPositive) separated
  have radiusPositive := comparison.first.radius_positive
  have densityIdentity : |comparison.density| = 2 * frequency * length ^ 2 / comparison.first.radius ^ 2 :=
    (eq_div_iff (sq_pos_of_pos radiusPositive).ne').mpr mass
  have inverseCube : distance⁻¹ ^ 3 ≤ (separation * length)⁻¹ ^ 3 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (mul_pos separationPositive lengthPositive) separated) 3
  let prefactor := 48 * constant * |comparison.density| * comparison.first.radius ^ 4 /
    (Real.pi * frequency * length)
  have prefactorNonnegative : 0 ≤ prefactor := by dsimp only [prefactor]; positivity
  have budgetNonnegative := comparison.spectralDifferenceBudget_nonnegative
  calc
    comparison.velocityCentroidCorrectionShapeEnvelope constant / (frequency * length) =
        prefactor * distance⁻¹ ^ 3 * comparison.spectralDifferenceBudget := by
      unfold velocityCentroidCorrectionShapeEnvelope
      dsimp only [prefactor, distance]
      ring
    _ ≤ prefactor * (separation * length)⁻¹ ^ 3 * comparison.spectralDifferenceBudget :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left inverseCube prefactorNonnegative) budgetNonnegative
    _ = _ := by
      dsimp only [prefactor]
      rw [densityIdentity]
      field_simp [frequencyPositive.ne', lengthPositive.ne', separationPositive.ne', radiusPositive.ne', Real.pi_ne_zero]
      <;> ring

theorem velocityCentroidCorrection_envelopes_normalized_le
    (comparison : MovingPatchSourceComparison) {frequency length separation constant : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (constantNonnegative : 0 ≤ constant)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2)
    (separated : separation * length ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖) :
    (comparison.velocityCentroidCorrectionCenterEnvelope (separation * length) +
      comparison.velocityCentroidCorrectionShapeEnvelope constant) / (frequency * length) ≤
      (comparison.first.radius ^ 2 / length ^ 2) *
        (24 * separation⁻¹ ^ 4 * (‖comparison.displacementDifference‖ / length) +
          96 * constant / Real.pi * separation⁻¹ ^ 3 * comparison.spectralDifferenceBudget) := by
  rw [add_div, comparison.velocityCentroidCorrectionCenterEnvelope_normalized
    frequencyPositive lengthPositive separationPositive mass, mul_add]
  exact add_le_add_left (comparison.velocityCentroidCorrectionShapeEnvelope_normalized_le
    frequencyPositive lengthPositive separationPositive constantNonnegative mass separated) _

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
