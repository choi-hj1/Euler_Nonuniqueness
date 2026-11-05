import EulerNonuniqueness.Section6.FourPointAngularImpulse

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointShapeImpulseVelocity (coefficient : ℝ) (positions : FourPointConfiguration) : ℝ :=
  -(star (fourPointArithmeticCenter (fourPointField coefficient positions)) * fourPointSignedMoment positions).re

theorem fourPointShapeImpulseVelocity_bound {base : FourPointConfiguration}
    (noncollision : FourPointNoncollision base) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 - base‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      |fourPointShapeImpulseVelocity coefficient positions| ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 4 := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, estimate⟩ :=
    fourPointArithmeticCenter_field_signedMoment_bound noncollision
  refine ⟨bound, boundNonnegative, radius, radiusPositive, ?_⟩
  intro coefficient positions centeredNoncollision centeredSmall momentSmall
  have centerControl := estimate coefficient positions centeredNoncollision centeredSmall momentSmall
  calc
    _ ≤ ‖star (fourPointArithmeticCenter (fourPointField coefficient positions)) * fourPointSignedMoment positions‖ := by
      simpa only [fourPointShapeImpulseVelocity, abs_neg] using Complex.abs_re_le_norm
        (star (fourPointArithmeticCenter (fourPointField coefficient positions)) * fourPointSignedMoment positions)
    _ = ‖fourPointArithmeticCenter (fourPointField coefficient positions)‖ * ‖fourPointSignedMoment positions‖ := by
      rw [norm_mul, norm_star]
    _ ≤ (bound * |coefficient| * ‖fourPointSignedMoment positions‖ / 4) * ‖fourPointSignedMoment positions‖ :=
      mul_le_mul_of_nonneg_right centerControl (norm_nonneg _)
    _ = _ := by ring

theorem fourPointShapeImpulse_actual_equation {trajectory : ℝ → FourPointConfiguration}
    {coefficient time : ℝ} (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => ‖(fourPointOddPart (trajectory current)).1‖ ^ 2 -
      ‖(fourPointOddPart (trajectory current)).2‖ ^ 2)
      (fourPointShapeImpulseVelocity coefficient (trajectory time)) time :=
  fourPointShapeImpulse_hasDerivAt noncollision equation

end EulerNonuniqueness.Section6
