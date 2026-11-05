import EulerNonuniqueness.Section6.RelativePointShapeChart
import EulerNonuniqueness.Section6.UniformPointShapeForcing

namespace EulerNonuniqueness.Section5

open EulerNonuniqueness.Section6

theorem reference_actual_field_shape_remainder :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      ∀ (frequency : ℝ) (positions : FourPointConfiguration) (field : ℂ → ℂ)
        (residual : ℂ × ℂ) (strainBound : ℝ),
      0 ≤ strainBound →
      (fourPointOddPart positions).1 ≠ 0 → (fourPointOddPart positions).2 ≠ 0 →
      ‖field (positions 0) - field (positions 1)‖ ≤ strainBound * ‖positions 0 - positions 1‖ →
      ‖field (positions 2) - field (positions 3)‖ ≤ strainBound * ‖positions 2 - positions 3‖ →
      |(pointShapeChart (fourPointOddPart positions).1 (fourPointOddPart positions).2).1| +
        |(pointShapeChart (fourPointOddPart positions).1 (fourPointOddPart positions).2).2| < radius →
      let point := fourPointOddPart positions
      let chart := pointShapeChart point.1 point.2
      let oddField := fourPointOddPart (fun label => field (positions label))
      let forcing := pointShapeForcing point.1 point.2 (oddField.1 + residual.1) (oddField.2 + residual.2)
      let velocity := shapeChartVelocity frequency chart + forcing
      |velocity.1 - 2 * Real.sqrt 2 * frequency * chart.1| +
        |velocity.2 + 2 * Real.sqrt 2 * frequency * chart.2| ≤
          bound * |frequency| * (|chart.1| + |chart.2|) ^ 2 + 12 * strainBound +
            2 * pointShapeForcingWeight point * ‖residual‖ := by
  obtain ⟨bound, boundNonnegative, radius, radiusPositive, nonlinearBound⟩ :=
    shapeChartVelocity_uniform_quadratic_remainder
  refine ⟨bound, boundNonnegative, min radius 1, lt_min radiusPositive (by norm_num), ?_⟩
  intro frequency positions field residual strainBound strainNonnegative positiveNonzero negativeNonzero
    positivePair negativePair chartSmall
  let point := fourPointOddPart positions
  let chart := pointShapeChart point.1 point.2
  let oddField := fourPointOddPart (fun label => field (positions label))
  let external := pointShapeForcing point.1 point.2 oddField.1 oddField.2
  let error := pointShapeForcing point.1 point.2 residual.1 residual.2
  have externalBound : |external.1| + |external.2| ≤ 12 * strainBound :=
    pointShapeForcing_odd_field_lipschitz_component_sum_le positions field strainNonnegative
      positiveNonzero negativeNonzero positivePair negativePair (chartSmall.le.trans (min_le_right _ _))
  have errorNorm : ‖error‖ ≤ pointShapeForcingWeight point * ‖residual‖ :=
    pointShapeForcing_norm_bound point.1 point.2 residual.1 residual.2
  have errorFirst : |error.1| ≤ ‖error‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le error
  have errorSecond : |error.2| ≤ ‖error‖ := by simpa only [Real.norm_eq_abs] using norm_snd_le error
  have errorBound : |error.1| + |error.2| ≤ 2 * pointShapeForcingWeight point * ‖residual‖ := by
    nlinarith
  have nonlinear := nonlinearBound frequency chart.1 chart.2 (chartSmall.trans_le (min_le_left _ _))
  have actualForcing : pointShapeForcing point.1 point.2 (oddField.1 + residual.1) (oddField.2 + residual.2) =
      external + error := pointShapeForcing_add _ _ _ _ _ _
  dsimp only
  change |(shapeChartVelocity frequency chart).1 +
      (pointShapeForcing point.1 point.2 (oddField.1 + residual.1) (oddField.2 + residual.2)).1 -
        2 * Real.sqrt 2 * frequency * chart.1| +
    |(shapeChartVelocity frequency chart).2 +
      (pointShapeForcing point.1 point.2 (oddField.1 + residual.1) (oddField.2 + residual.2)).2 +
        2 * Real.sqrt 2 * frequency * chart.2| ≤ _
  rw [actualForcing]
  have firstBound : |(shapeChartVelocity frequency chart).1 + (external + error).1 -
      2 * Real.sqrt 2 * frequency * chart.1| ≤
      |(shapeChartVelocity frequency chart).1 - 2 * Real.sqrt 2 * frequency * chart.1| + |external.1| + |error.1| := by
    convert (abs_add_le ((shapeChartVelocity frequency chart).1 -
      2 * Real.sqrt 2 * frequency * chart.1 + external.1) error.1).trans
      (add_le_add_right (abs_add_le _ _) _) using 1 <;> congr 1 <;> dsimp only [Prod.fst_add] <;> ring
  have secondBound : |(shapeChartVelocity frequency chart).2 + (external + error).2 +
      2 * Real.sqrt 2 * frequency * chart.2| ≤
      |(shapeChartVelocity frequency chart).2 + 2 * Real.sqrt 2 * frequency * chart.2| + |external.2| + |error.2| := by
    convert (abs_add_le ((shapeChartVelocity frequency chart).2 +
      2 * Real.sqrt 2 * frequency * chart.2 + external.2) error.2).trans
      (add_le_add_right (abs_add_le _ _) _) using 1 <;> congr 1 <;> dsimp only [Prod.snd_add] <;> ring
  linarith

end EulerNonuniqueness.Section5
