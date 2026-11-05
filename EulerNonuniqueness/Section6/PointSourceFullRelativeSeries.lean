import EulerNonuniqueness.Section6.PointSourceRelativeSeries
import EulerNonuniqueness.Section6.PointSourceTranslationSeries
import EulerNonuniqueness.General.TwoGeometricMajorants

noncomputable section

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

theorem pointSourceTaylorCoefficient_full_relative_summable_and_tsum_le
    (firstPositions secondPositions : FourPointConfiguration) (first second : ℂ) (circulation : ℝ)
    {receiverRadius radius travel distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : radius + travel + distance ≤ ‖first‖)
    (firstPositionBound : ∀ patch, ‖firstPositions patch‖ ≤ radius)
    (secondPositionBound : ∀ patch, ‖secondPositions patch‖ ≤ radius)
    (receiverDifference : ‖second - first‖ ≤ travel)
    (firstRatio : 4 * weight * receiverRadius / distance < 1)
    (secondRatio : 8 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius firstPositions first power -
        pointSourceTaylorCoefficient circulation receiverRadius secondPositions second power‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius firstPositions first power -
        pointSourceTaylorCoefficient circulation receiverRadius secondPositions second power‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment firstPositions - fourPointSignedMoment secondPositions‖ +
          32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖firstPositions patch - secondPositions patch‖)) *
            (1 - 4 * weight * receiverRadius / distance)⁻¹ +
      (weight * (|circulation| / (2 * Real.pi)) *
        (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment secondPositions‖ +
          512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖secondPositions patch‖) * ‖first - second‖) *
            (1 - 8 * weight * receiverRadius / distance)⁻¹ := by
  have firstSeparated : radius + distance ≤ ‖first‖ := by linarith
  have pointwise (power : ℕ) : weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius firstPositions first power -
        pointSourceTaylorCoefficient circulation receiverRadius secondPositions second power‖ ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment firstPositions - fourPointSignedMoment secondPositions‖ +
          32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖firstPositions patch - secondPositions patch‖)) *
            (4 * weight * receiverRadius / distance) ^ power +
      (weight * (|circulation| / (2 * Real.pi)) *
        (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment secondPositions‖ +
          512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖secondPositions patch‖) * ‖first - second‖) *
            (8 * weight * receiverRadius / distance) ^ power := by
    have configuration := pointSourceTaylorCoefficient_relative_weighted_term_le firstPositions secondPositions first
      power circulation receiverNonnegative radiusNonnegative positive weightNonnegative firstSeparated
      firstPositionBound secondPositionBound
    have translation := pointSourceTaylorCoefficient_translation_weighted_term_le secondPositions first first second
      power circulation receiverNonnegative radiusNonnegative travelNonnegative positive weightNonnegative separated
      secondPositionBound (by simpa using travelNonnegative) receiverDifference
    have triangle := norm_sub_le_norm_sub_add_norm_sub
      (pointSourceTaylorCoefficient circulation receiverRadius firstPositions first power)
      (pointSourceTaylorCoefficient circulation receiverRadius secondPositions first power)
      (pointSourceTaylorCoefficient circulation receiverRadius secondPositions second power)
    exact (mul_le_mul_of_nonneg_left triangle (pow_nonneg weightNonnegative (power + 1))).trans
      (by rw [mul_add]; exact add_le_add configuration translation)
  exact EulerNonuniqueness.General.summable_and_tsum_le_of_two_geometric_majorants
    (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius firstPositions first power -
        pointSourceTaylorCoefficient circulation receiverRadius secondPositions second power‖)
    (weight * (|circulation| / (2 * Real.pi)) *
      (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment firstPositions - fourPointSignedMoment secondPositions‖ +
        32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖firstPositions patch - secondPositions patch‖))
    (weight * (|circulation| / (2 * Real.pi)) *
      (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment secondPositions‖ +
        512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖secondPositions patch‖) * ‖first - second‖)
    (4 * weight * receiverRadius / distance) (8 * weight * receiverRadius / distance)
    (fun power => by positivity) (by positivity) firstRatio (by positivity) secondRatio pointwise

end EulerNonuniqueness.Section6
