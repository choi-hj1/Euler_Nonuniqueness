import EulerNonuniqueness.Section6.PointSourceTranslationCoefficient

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointSourceTaylorCoefficient_translation_summable_and_tsum_le (positions : FourPointConfiguration)
    (anchor first second : ℂ) (circulation : ℝ) {receiverRadius radius travel distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius)
    (travelNonnegative : 0 ≤ travel) (positive : 0 < distance) (weightNonnegative : 0 ≤ weight)
    (separated : radius + travel + distance ≤ ‖anchor‖)
    (positionBound : ∀ patch, ‖positions patch‖ ≤ radius)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel)
    (small : 8 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions first power -
        pointSourceTaylorCoefficient circulation receiverRadius positions second power‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius positions first power -
        pointSourceTaylorCoefficient circulation receiverRadius positions second power‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment positions‖ +
          512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖) *
        (1 - 8 * weight * receiverRadius / distance)⁻¹ := by
  have ratioNonnegative : 0 ≤ 8 * weight * receiverRadius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one ratioNonnegative small).mul_left
    (weight * (|circulation| / (2 * Real.pi)) *
      (32 * distance⁻¹ ^ 4 * ‖fourPointSignedMoment positions‖ +
        512 * distance⁻¹ ^ 5 * radius * ∑ patch : Fin 4, ‖positions patch‖) * ‖first - second‖)
  have bound (power : ℕ) := pointSourceTaylorCoefficient_translation_weighted_term_le positions anchor first second power
    circulation receiverNonnegative radiusNonnegative travelNonnegative positive weightNonnegative separated positionBound
    firstBound secondBound
  have summable := Summable.of_nonneg_of_le (fun power => by positivity) bound geometric
  refine ⟨summable, ?_⟩
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative small] using
    summable.tsum_le_tsum bound geometric

end EulerNonuniqueness.Section6
