import EulerNonuniqueness.Section6.RelativePointShapeForcing

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

theorem pointShapeRatio_le_two_rhombus_of_small_chart (positive negative : ℂ)
    (small : |(pointShapeChart positive negative).1| + |(pointShapeChart positive negative).2| ≤ 1) :
    pointShapeRatio positive negative ≤ 2 * rhombusRatio := by
  have reconstruction := (shapeChart_reconstruction (pointShapeRatio positive negative)
    (pointShapeAngle positive negative)).1
  change rhombusRatio * (1 + (pointShapeChart positive negative).1 +
    (pointShapeChart positive negative).2) = pointShapeRatio positive negative at reconstruction
  have sumBound : 1 + (pointShapeChart positive negative).1 + (pointShapeChart positive negative).2 ≤ 2 := by
    linarith [le_abs_self (pointShapeChart positive negative).1, le_abs_self (pointShapeChart positive negative).2]
  calc
    _ = rhombusRatio * (1 + (pointShapeChart positive negative).1 + (pointShapeChart positive negative).2) :=
      reconstruction.symm
    _ ≤ rhombusRatio * 2 := mul_le_mul_of_nonneg_left sumBound rhombusRatio_pos.le
    _ = _ := by ring

theorem pointShapeForcing_odd_field_lipschitz_component_sum_le
    (positions : FourPointConfiguration) (field : ℂ → ℂ) {strainBound : ℝ}
    (strainNonnegative : 0 ≤ strainBound)
    (positiveNonzero : (fourPointOddPart positions).1 ≠ 0)
    (negativeNonzero : (fourPointOddPart positions).2 ≠ 0)
    (positivePair : ‖field (positions 0) - field (positions 1)‖ ≤ strainBound * ‖positions 0 - positions 1‖)
    (negativePair : ‖field (positions 2) - field (positions 3)‖ ≤ strainBound * ‖positions 2 - positions 3‖)
    (small : |(pointShapeChart (fourPointOddPart positions).1 (fourPointOddPart positions).2).1| +
      |(pointShapeChart (fourPointOddPart positions).1 (fourPointOddPart positions).2).2| ≤ 1) :
    let forcing := pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
      (fourPointOddPart (fun label => field (positions label))).1
      (fourPointOddPart (fun label => field (positions label))).2
    |forcing.1| + |forcing.2| ≤ 12 * strainBound := by
  dsimp only
  have pairBound := pointShapeForcing_odd_field_lipschitz_norm_le positions field
    strainNonnegative positiveNonzero negativeNonzero positivePair negativePair
    (pointShapeRatio_le_two_rhombus_of_small_chart _ _ small)
  have firstBound := norm_fst_le (pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
    (fourPointOddPart (fun label => field (positions label))).1
    (fourPointOddPart (fun label => field (positions label))).2)
  have secondBound := norm_snd_le (pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
    (fourPointOddPart (fun label => field (positions label))).1
    (fourPointOddPart (fun label => field (positions label))).2)
  simp only [Real.norm_eq_abs] at firstBound secondBound
  linarith

end EulerNonuniqueness.Section6
