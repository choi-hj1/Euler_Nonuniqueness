import EulerNonuniqueness.Section6.PointSourceRelativeCoefficient

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointSourceTaylorCoefficient_relative_summable_and_tsum_le (first second : FourPointConfiguration)
    (displacement : ℂ) (circulation : ℝ) {receiverRadius radius distance weight : ℝ}
    (receiverNonnegative : 0 ≤ receiverRadius) (radiusNonnegative : 0 ≤ radius) (positive : 0 < distance)
    (weightNonnegative : 0 ≤ weight) (separated : radius + distance ≤ ‖displacement‖)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius)
    (secondBound : ∀ patch, ‖second patch‖ ≤ radius)
    (small : 4 * weight * receiverRadius / distance < 1) :
    Summable (fun power : ℕ => weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius first displacement power -
        pointSourceTaylorCoefficient circulation receiverRadius second displacement power‖) ∧
    (∑' power : ℕ, weight ^ (power + 1) *
      ‖pointSourceTaylorCoefficient circulation receiverRadius first displacement power -
        pointSourceTaylorCoefficient circulation receiverRadius second displacement power‖) ≤
      (weight * (|circulation| / (2 * Real.pi)) *
        (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
          32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖first patch - second patch‖)) *
        (1 - 4 * weight * receiverRadius / distance)⁻¹ := by
  have ratioNonnegative : 0 ≤ 4 * weight * receiverRadius / distance := by positivity
  have geometric := (summable_geometric_of_lt_one ratioNonnegative small).mul_left
    (weight * (|circulation| / (2 * Real.pi)) *
      (4 * distance⁻¹ ^ 3 * ‖fourPointSignedMoment first - fourPointSignedMoment second‖ +
        32 * distance⁻¹ ^ 4 * radius * ∑ patch : Fin 4, ‖first patch - second patch‖))
  have bound (power : ℕ) := pointSourceTaylorCoefficient_relative_weighted_term_le first second displacement
    power circulation receiverNonnegative radiusNonnegative positive weightNonnegative separated firstBound secondBound
  have summable := Summable.of_nonneg_of_le (fun power => by positivity) bound geometric
  refine ⟨summable, ?_⟩
  simpa only [tsum_mul_left, tsum_geometric_of_lt_one ratioNonnegative small] using
    summable.tsum_le_tsum bound geometric

end EulerNonuniqueness.Section6
