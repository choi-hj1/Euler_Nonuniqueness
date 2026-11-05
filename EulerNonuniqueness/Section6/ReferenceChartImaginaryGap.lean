import EulerNonuniqueness.Section6.ReferenceChartAnnulus
import EulerNonuniqueness.Section6.ReferenceShapeChartDomain

noncomputable section

namespace EulerNonuniqueness.Section6

theorem pointShapeChart_reference_imaginary_gap (positive negative : ℂ)
    (small : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4)
    (upper : 0 < (negative / positive).im) :
    (1 / 8 : ℝ) ≤ (negative / positive).im := by
  obtain ⟨positiveNonzero, negativeNonzero, ratioLower, _⟩ := pointShapeChart_reference_annulus positive negative small
  have quotientLower : (1 / 4 : ℝ) ≤ ‖negative / positive‖ := by
    simpa only [norm_div] using ratioLower
  have left := pointShapeChart_leftHalfPlane_of_small positiveNonzero negativeNonzero small
  simp only [pow_two, Complex.mul_re] at left
  have normIdentity : ‖negative / positive‖ ^ 2 =
      (negative / positive).re * (negative / positive).re +
      (negative / positive).im * (negative / positive).im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  by_contra failure
  have imaginarySmall : (negative / positive).im < 1 / 8 := lt_of_not_ge failure
  nlinarith [norm_nonneg (negative / positive)]

end EulerNonuniqueness.Section6
