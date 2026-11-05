import EulerNonuniqueness.Section6.PairedCenterRelativeField
import EulerNonuniqueness.Section6.FourPointAngularImpulse

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointCenteredDilationRate (coefficient : ℝ) (positions : FourPointConfiguration) : ℝ :=
  -(star (fourPointArithmeticCenter (fourPointField coefficient positions)) * fourPointSignedMoment positions).re

theorem fourPointShapeImpulse_hasDerivAt_centeredDilationRate
    {trajectory : ℝ → FourPointConfiguration} {coefficient time : ℝ}
    (noncollision : FourPointNoncollision (trajectory time))
    (equation : ∀ target, HasDerivAt (fun current => trajectory current target)
      (fourPointField coefficient (trajectory time) target) time) :
    HasDerivAt (fun current => ‖(fourPointOddPart (trajectory current)).1‖ ^ 2 -
      ‖(fourPointOddPart (trajectory current)).2‖ ^ 2)
      (fourPointCenteredDilationRate coefficient (trajectory time)) time :=
  fourPointShapeImpulse_hasDerivAt noncollision equation

theorem fourPointCenteredDilationRate_relative_signedMoment_bound
    (coefficient : ℝ) (first second : FourPointConfiguration) {gap radius : ℝ}
    (gapPositive : 0 < gap) (radiusNonnegative : 0 ≤ radius)
    (firstBound : ∀ patch, ‖first patch‖ ≤ radius) (secondBound : ∀ patch, ‖second patch‖ ≤ radius)
    (firstSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gap ≤ ‖first positive - first negative‖)
    (secondSeparated : ∀ positive negative : Fin 4, positive.val < 2 → 2 ≤ negative.val →
      gap ≤ ‖second positive - second negative‖) :
    |fourPointCenteredDilationRate coefficient first - fourPointCenteredDilationRate coefficient second| ≤
      |coefficient| *
        ((‖fourPointSignedMoment first‖ + ‖fourPointSignedMoment second‖) *
          ‖fourPointSignedMoment first - fourPointSignedMoment second‖ / gap ^ 2 +
        8 * radius * ‖fourPointSignedMoment first‖ * ‖fourPointSignedMoment second‖ * ‖first - second‖ / gap ^ 4) := by
  let firstVelocity := fourPointArithmeticCenter (fourPointField coefficient first)
  let secondVelocity := fourPointArithmeticCenter (fourPointField coefficient second)
  have identity : fourPointCenteredDilationRate coefficient first - fourPointCenteredDilationRate coefficient second =
      -((star firstVelocity - star secondVelocity) * fourPointSignedMoment first +
        star secondVelocity * (fourPointSignedMoment first - fourPointSignedMoment second)).re := by
    simp only [fourPointCenteredDilationRate, Complex.add_re, Complex.sub_re, mul_sub, sub_mul]
    ring
  rw [identity, abs_neg]
  have productBound := (Complex.abs_re_le_norm _).trans (norm_add_le
    ((star firstVelocity - star secondVelocity) * fourPointSignedMoment first)
    (star secondVelocity * (fourPointSignedMoment first - fourPointSignedMoment second)))
  simp only [norm_mul] at productBound
  have conjugateDifference : ‖star firstVelocity - star secondVelocity‖ = ‖firstVelocity - secondVelocity‖ := by
    rw [← star_sub, norm_star]
  rw [conjugateDifference, norm_star] at productBound
  have difference := fourPointArithmeticCenter_field_relative_signedMoment_bound coefficient first second
    gapPositive radiusNonnegative firstBound secondBound firstSeparated secondSeparated
  have reference := fourPointArithmeticCenter_field_signedMoment_gap_bound coefficient second gapPositive secondSeparated
  have total := productBound.trans (add_le_add
    (mul_le_mul_of_nonneg_right difference (norm_nonneg (fourPointSignedMoment first)))
    (mul_le_mul_of_nonneg_right reference (norm_nonneg (fourPointSignedMoment first - fourPointSignedMoment second))))
  convert total using 1 <;> dsimp only [firstVelocity, secondVelocity] <;> ring

end EulerNonuniqueness.Section6
