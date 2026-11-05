import EulerNonuniqueness.Section6.ReferenceChartAnnulus
import EulerNonuniqueness.Section6.UniformPointShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem pointShapeForcingWeight_reference_le {positive negative : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (differenceLower : length ^ 2 / 2 ≤ ‖positive‖ ^ 2 - ‖negative‖ ^ 2)
    (small : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1 / 4) :
    pointShapeForcingWeight (positive, negative) ≤ 30 / length := by
  obtain ⟨positiveNonzero, negativeNonzero, ratioLower, ratioUpper⟩ :=
    pointShapeChart_reference_annulus positive negative small
  have positiveNorm : 0 < ‖positive‖ := norm_pos_iff.mpr positiveNonzero
  have negativeNorm : 0 < ‖negative‖ := norm_pos_iff.mpr negativeNonzero
  have positiveLower : length / 2 ≤ ‖positive‖ := by
    nlinarith [sq_nonneg ‖negative‖, norm_nonneg positive]
  have negativeLower : length / 8 ≤ ‖negative‖ := by
    have comparison := (le_div_iff₀ positiveNorm).mp ratioLower
    linarith
  have positiveInverse : 1 / ‖positive‖ ≤ 2 / length := by
    apply (div_le_div_iff₀ positiveNorm lengthPositive).mpr
    linarith
  have negativeInverse : 1 / ‖negative‖ ≤ 8 / length := by
    apply (div_le_div_iff₀ negativeNorm lengthPositive).mpr
    linarith
  have reconstruction := (shapeChart_reconstruction (pointShapeRatio positive negative)
    (pointShapeAngle positive negative)).1
  change rhombusRatio * (1 + (pointShapeChart positive negative).1 +
    (pointShapeChart positive negative).2) = pointShapeRatio positive negative at reconstruction
  have ratioBound : pointShapeRatio positive negative / rhombusRatio + 1 ≤ 3 := by
    have ratioLe : pointShapeRatio positive negative / rhombusRatio ≤ 2 := by
      apply (div_le_iff₀ rhombusRatio_pos).mpr
      exact pointShapeRatio_le_two_rhombus_of_small_chart positive negative (by linarith)
    linarith
  have sumBound : 1 / ‖negative‖ + 1 / ‖positive‖ ≤ 10 / length := by
    exact (add_le_add negativeInverse positiveInverse).trans_eq (by ring)
  change (pointShapeRatio positive negative / rhombusRatio + 1) *
    (1 / ‖negative‖ + 1 / ‖positive‖) ≤ _
  exact (mul_le_mul ratioBound sumBound (by positivity) (by norm_num)).trans_eq (by ring)

end EulerNonuniqueness.Section6
