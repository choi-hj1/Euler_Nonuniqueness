import EulerNonuniqueness.Section6.FourPointInversePowerRelative
import EulerNonuniqueness.Section6.SignedInversePowerTranslation
import EulerNonuniqueness.Section6.PairedPhysicalStrain

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

theorem fourPointExternalPointVelocity_eq_inverse_sum (coefficient : ℝ)
    (positions : FourPointConfiguration) (location : ℂ) :
    fourPointExternalPointVelocity coefficient positions location =
      (Complex.I * (coefficient : ℂ)) *
        ∑ patch : Fin 4, fourPointSign patch • (star (location - positions patch))⁻¹ := by
  rw [fourPointExternalPointVelocity_literal]
  simp only [Complex.real_smul, Complex.ofReal_mul, div_eq_mul_inv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro patch _
  ring

theorem fourPointExternalPointVelocity_configuration_difference_bound
    (first second : FourPointConfiguration) (displacement : ℂ) (coefficient : ℝ)
    {radius distance : ℝ} (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius) :
    ‖fourPointExternalPointVelocity coefficient first displacement -
      fourPointExternalPointVelocity coefficient second displacement‖ ≤
      |coefficient| * (distance⁻¹ ^ 2 * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
        2 * distance⁻¹ ^ 3 * radius * ∑ patch : Fin 4, ‖first patch - second patch‖) := by
  have actual := fourPoint_inverse_power_relative_bound first second displacement 0
    radiusNonnegative positive separated firstBound secondBound
  simp only [Nat.cast_zero, zero_add, Nat.reduceAdd, pow_one, one_mul] at actual
  rw [fourPointExternalPointVelocity_eq_inverse_sum, fourPointExternalPointVelocity_eq_inverse_sum,
    ← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left actual (abs_nonneg coefficient)

theorem fourPointExternalPointVelocity_translation_difference_bound
    (positions : FourPointConfiguration) (anchor first second : ℂ) (coefficient : ℝ)
    {radius travel distance : ℝ} (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (separated : radius + travel + distance ≤ ‖anchor‖)
    (positionBound : ∀ patch, ‖positions patch‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel) :
    ‖fourPointExternalPointVelocity coefficient positions first -
      fourPointExternalPointVelocity coefficient positions second‖ ≤
      |coefficient| *
        (2 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment positions‖ +
          6 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖ := by
  have zeroMass : ∑ patch : Fin 4, fourPointSign patch = 0 := by
    norm_num [fourPointSign, Fin.sum_univ_succ]
  have momentIdentity : (∑ patch : Fin 4, fourPointSign patch • positions patch) =
      fourPointSignedMoment positions := by
    simp only [Complex.real_smul, fourPointSignedMoment]
  have absoluteSign (patch : Fin 4) : |fourPointSign patch| = 1 := by
    unfold fourPointSign
    split_ifs <;> norm_num
  have actual := signed_inverse_power_translation_bound Finset.univ fourPointSign positions zeroMass
    anchor first second 0 radiusNonnegative travelNonnegative positive separated
    (fun patch _ => positionBound patch) firstBound secondBound
  simp only [momentIdentity, absoluteSign, one_mul, Nat.cast_zero, zero_add,
    Nat.reduceAdd, pow_one, one_mul] at actual
  rw [fourPointExternalPointVelocity_eq_inverse_sum, fourPointExternalPointVelocity_eq_inverse_sum,
    ← mul_sub, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left actual (abs_nonneg coefficient)).trans_eq (by ring)

theorem fourPointExternalPointVelocity_full_relative_bound
    (firstPositions secondPositions : FourPointConfiguration) (first second : ℂ) (coefficient : ℝ)
    {radius travel distance : ℝ} (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (separated : radius + travel + distance ≤ ‖first‖)
    (firstPositionBound : ∀ patch, ‖firstPositions patch‖ ≤ radius)
    (secondPositionBound : ∀ patch, ‖secondPositions patch‖ ≤ radius)
    (receiverDifference : ‖second - first‖ ≤ travel) :
    ‖fourPointExternalPointVelocity coefficient firstPositions first -
      fourPointExternalPointVelocity coefficient secondPositions second‖ ≤
      |coefficient| *
        (distance⁻¹ ^ 2 * ‖fourPointSignedMoment firstPositions - fourPointSignedMoment secondPositions‖ +
          2 * distance⁻¹ ^ 3 * radius * ∑ patch : Fin 4, ‖firstPositions patch - secondPositions patch‖) +
      |coefficient| *
        (2 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment secondPositions‖ +
          6 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖secondPositions patch‖) * ‖first - second‖ := by
  have configuration := fourPointExternalPointVelocity_configuration_difference_bound
    firstPositions secondPositions first coefficient radiusNonnegative positive
    (by linarith) firstPositionBound secondPositionBound
  have translation := fourPointExternalPointVelocity_translation_difference_bound
    secondPositions first first second coefficient radiusNonnegative travelNonnegative positive separated
    secondPositionBound (by simpa using travelNonnegative) receiverDifference
  exact (norm_sub_le_norm_sub_add_norm_sub
    (fourPointExternalPointVelocity coefficient firstPositions first)
    (fourPointExternalPointVelocity coefficient secondPositions first)
    (fourPointExternalPointVelocity coefficient secondPositions second)).trans
      (add_le_add configuration translation)

end EulerNonuniqueness.Section6
