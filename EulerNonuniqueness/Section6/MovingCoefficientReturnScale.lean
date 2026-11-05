import EulerNonuniqueness.Section6.MovingPatchCenteredSourceSeries
import EulerNonuniqueness.Section6.MovingPatchVelocityReturnScale

noncomputable section

namespace EulerNonuniqueness.Paper.MovingPatchSourceComparison

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem centerDifferenceEnvelope_normalized
    (comparison : MovingPatchSourceComparison) {frequency length separation weight : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2) :
    comparison.centerDifferenceEnvelope (separation * length) weight / frequency =
      4 * weight * separation⁻¹ ^ 3 * (‖comparison.displacementDifference‖ / length) := by
  have radiusPositive := comparison.first.radius_positive
  have densityIdentity : |comparison.density| = 2 * frequency * length ^ 2 / comparison.first.radius ^ 2 :=
    (eq_div_iff (sq_pos_of_pos radiusPositive).ne').mpr mass
  unfold centerDifferenceEnvelope
  rw [densityIdentity]
  field_simp [frequencyPositive.ne', lengthPositive.ne', separationPositive.ne', radiusPositive.ne', Real.pi_ne_zero]
  <;> ring

theorem centeredShapeDifferenceEnvelope_normalized_le
    (comparison : MovingPatchSourceComparison) {frequency length separation constant weight : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (constantNonnegative : 0 ≤ constant) (weightNonnegative : 0 ≤ weight)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2)
    (separated : separation * length ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖) :
    comparison.centeredShapeDifferenceEnvelope constant weight / frequency ≤
      (constant * 96 ^ 2 * weight / Real.pi) * separation⁻¹ ^ 4 *
        (comparison.first.radius ^ 2 / length ^ 2) * comparison.spectralDifferenceBudget := by
  let distance := ‖comparison.secondReceiver - comparison.second.center comparison.time‖
  have distancePositive : 0 < distance := lt_of_lt_of_le (mul_pos separationPositive lengthPositive) separated
  have radiusPositive := comparison.first.radius_positive
  have densityIdentity : |comparison.density| = 2 * frequency * length ^ 2 / comparison.first.radius ^ 2 :=
    (eq_div_iff (sq_pos_of_pos radiusPositive).ne').mpr mass
  have inverseFourth : distance⁻¹ ^ 4 ≤ (separation * length)⁻¹ ^ 4 :=
    pow_le_pow_left₀ (by positivity) (inv_anti₀ (mul_pos separationPositive lengthPositive) separated) 4
  let prefactor := constant * 96 ^ 2 * weight * |comparison.density| * comparison.first.radius ^ 4 /
    (2 * Real.pi * frequency)
  have prefactorNonnegative : 0 ≤ prefactor := by dsimp only [prefactor]; positivity
  have budgetNonnegative := comparison.spectralDifferenceBudget_nonnegative
  calc
    comparison.centeredShapeDifferenceEnvelope constant weight / frequency =
        prefactor * distance⁻¹ ^ 4 * comparison.spectralDifferenceBudget := by
      unfold centeredShapeDifferenceEnvelope
      dsimp only [prefactor, distance]
      field_simp [distancePositive.ne']
      <;> ring
    _ ≤ prefactor * (separation * length)⁻¹ ^ 4 * comparison.spectralDifferenceBudget :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left inverseFourth prefactorNonnegative) budgetNonnegative
    _ = _ := by
      dsimp only [prefactor]
      rw [densityIdentity]
      field_simp [frequencyPositive.ne', lengthPositive.ne', separationPositive.ne', radiusPositive.ne', Real.pi_ne_zero]
      <;> ring

theorem centeredDifferenceEnvelopes_normalized_le
    (comparison : MovingPatchSourceComparison) {frequency length separation constant weight : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (separationPositive : 0 < separation)
    (constantNonnegative : 0 ≤ constant) (weightNonnegative : 0 ≤ weight)
    (mass : |comparison.density| * comparison.first.radius ^ 2 = 2 * frequency * length ^ 2)
    (separated : separation * length ≤ ‖comparison.secondReceiver - comparison.second.center comparison.time‖) :
    (comparison.centerDifferenceEnvelope (separation * length) weight +
      comparison.centeredShapeDifferenceEnvelope constant weight) / frequency ≤
      4 * weight * separation⁻¹ ^ 3 * (‖comparison.displacementDifference‖ / length) +
        (constant * 96 ^ 2 * weight / Real.pi) * separation⁻¹ ^ 4 *
          (comparison.first.radius ^ 2 / length ^ 2) * comparison.spectralDifferenceBudget := by
  rw [add_div, comparison.centerDifferenceEnvelope_normalized frequencyPositive lengthPositive separationPositive mass]
  exact add_le_add_left (comparison.centeredShapeDifferenceEnvelope_normalized_le
    frequencyPositive lengthPositive separationPositive constantNonnegative weightNonnegative mass separated) _

end EulerNonuniqueness.Paper.MovingPatchSourceComparison
