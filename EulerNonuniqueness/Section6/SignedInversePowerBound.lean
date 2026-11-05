import EulerNonuniqueness.Section6.SignedInversePowerRelative

noncomputable section

namespace EulerNonuniqueness.Section6

theorem signed_inverse_power_bound {Index : Type*}
    (selected : Finset Index) (weights : Index → ℝ) (positions : Index → ℂ)
    (zeroMass : ∑ index ∈ selected, weights index = 0)
    (displacement : ℂ) (power : ℕ) {radius distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (positionBound : ∀ index ∈ selected, ‖positions index‖ ≤ radius) :
    ‖∑ index ∈ selected, weights index • (star (displacement - positions index))⁻¹ ^ (power + 1)‖ ≤
      ((power + 1 : ℝ) * distance⁻¹ ^ (power + 2)) *
        ‖∑ index ∈ selected, weights index • positions index‖ +
      ((power + 1 : ℝ) * (power + 2 : ℝ) * distance⁻¹ ^ (power + 3) * radius) *
        ∑ index ∈ selected, |weights index| * ‖positions index‖ := by
  have constantZero :
      (∑ index ∈ selected, weights index • (star displacement)⁻¹ ^ (power + 1)) = 0 := by
    rw [← Finset.sum_smul, zeroMass, zero_smul]
  simpa only [sub_zero, constantZero] using
    signed_inverse_power_relative_bound selected weights positions (fun _ => 0) displacement power
      radiusNonnegative positive separated positionBound (fun _ _ => by simpa using radiusNonnegative)

end EulerNonuniqueness.Section6
