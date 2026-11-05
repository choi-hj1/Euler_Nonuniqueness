import EulerNonuniqueness.Section6.PointShapeForcingBound

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def pointShapeForcingWeight (point : ℂ × ℂ) : ℝ :=
  (pointShapeRatio point.1 point.2 / rhombusRatio + 1) * (1 / ‖point.2‖ + 1 / ‖point.1‖)

theorem pointShapeForcingWeight_nonnegative (point : ℂ × ℂ) :
    0 ≤ pointShapeForcingWeight point := by
  have ratioNonnegative : 0 ≤ pointShapeRatio point.1 point.2 := by dsimp [pointShapeRatio]; positivity
  exact mul_nonneg (add_nonneg (div_nonneg ratioNonnegative rhombusRatio_pos.le) zero_le_one) (by positivity)

theorem pointShapeForcingWeight_continuousAt {point : ℂ × ℂ}
    (positiveNonzero : point.1 ≠ 0) (negativeNonzero : point.2 ≠ 0) :
    ContinuousAt pointShapeForcingWeight point := by
  have positiveNormNonzero := norm_ne_zero_iff.mpr positiveNonzero
  have negativeNormNonzero := norm_ne_zero_iff.mpr negativeNonzero
  unfold pointShapeForcingWeight pointShapeRatio
  fun_prop (disch := first | exact positiveNormNonzero | exact negativeNormNonzero |
    exact pow_ne_zero 2 positiveNormNonzero | exact rhombusRatio_pos.ne')

theorem pointShapeForcing_uniform_bound {point : ℂ × ℂ}
    (positiveNonzero : point.1 ≠ 0) (negativeNonzero : point.2 ≠ 0) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ current forcing : ℂ × ℂ,
      ‖current - point‖ < radius →
      ‖pointShapeForcing current.1 current.2 forcing.1 forcing.2‖ ≤ bound * ‖forcing‖ := by
  have continuous := pointShapeForcingWeight_continuousAt positiveNonzero negativeNonzero
  obtain ⟨radius, radiusPositive, estimate⟩ := Metric.continuousAt_iff.mp continuous 1 (by norm_num)
  refine ⟨pointShapeForcingWeight point + 1, by have nonnegative := pointShapeForcingWeight_nonnegative point; positivity,
    radius, radiusPositive, ?_⟩
  intro current forcing currentSmall
  have weightSmall := estimate (by simpa only [dist_eq_norm] using currentSmall)
  have weightBound : pointShapeForcingWeight current ≤ pointShapeForcingWeight point + 1 := by
    rw [Real.dist_eq] at weightSmall
    linarith [le_abs_self (pointShapeForcingWeight current - pointShapeForcingWeight point)]
  exact (pointShapeForcing_norm_bound current.1 current.2 forcing.1 forcing.2).trans
    (by simpa only [pointShapeForcingWeight, Prod.mk.eta] using
      mul_le_mul_of_nonneg_right weightBound (norm_nonneg forcing))

theorem fourPointShape_uniform_internalForcing_bound {positive negative : ℂ}
    (noncollision : FourPointNoncollision (centrallySymmetricFourPoint positive negative)) :
    ∃ bound ≥ (0 : ℝ), ∃ radius > (0 : ℝ), ∀ coefficient : ℝ,
      ∀ positions : FourPointConfiguration,
      FourPointNoncollision (centrallySymmetricFourPoint (fourPointOddPart positions).1
        (fourPointOddPart positions).2) →
      ‖centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 -
        centrallySymmetricFourPoint positive negative‖ < radius →
      ‖fourPointSignedMoment positions‖ < 4 * radius →
      ‖pointShapeForcing (fourPointOddPart positions).1 (fourPointOddPart positions).2
          (fourPointOddInternalError coefficient positions).1 (fourPointOddInternalError coefficient positions).2‖ ≤
        bound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16 := by
  obtain ⟨positiveNonzero, negativeNonzero, _, _⟩ :=
    centrallySymmetricFourPoint_noncollision_conditions noncollision
  obtain ⟨fieldBound, fieldBoundNonnegative, fieldRadius, fieldRadiusPositive, fieldEstimate⟩ :=
    fourPointOddInternalError_bound noncollision
  obtain ⟨chartBound, chartBoundNonnegative, chartRadius, chartRadiusPositive, chartEstimate⟩ :=
    pointShapeForcing_uniform_bound (point := (positive, negative)) positiveNonzero negativeNonzero
  refine ⟨chartBound * fieldBound, mul_nonneg chartBoundNonnegative fieldBoundNonnegative,
    min fieldRadius chartRadius, lt_min fieldRadiusPositive chartRadiusPositive, ?_⟩
  intro coefficient positions centeredNoncollision centeredSmall momentSmall
  have fieldControl := fieldEstimate coefficient positions centeredNoncollision
    (centeredSmall.trans_le (min_le_left _ _))
    (momentSmall.trans_le (mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)))
  have projectionControl := fourPointOddPart_norm_le
    (centrallySymmetricFourPoint (fourPointOddPart positions).1 (fourPointOddPart positions).2 -
      centrallySymmetricFourPoint positive negative)
  rw [fourPointOddPart_sub, fourPointOddPart_central, fourPointOddPart_central, Prod.mk.eta] at projectionControl
  have chartSmall : ‖fourPointOddPart positions - (positive, negative)‖ < chartRadius :=
    projectionControl.trans_lt (centeredSmall.trans_le (min_le_right _ _))
  have chartControl := chartEstimate (fourPointOddPart positions) (fourPointOddInternalError coefficient positions) chartSmall
  calc
    _ ≤ chartBound * ‖fourPointOddInternalError coefficient positions‖ := chartControl
    _ ≤ chartBound * (fieldBound * |coefficient| * ‖fourPointSignedMoment positions‖ ^ 2 / 16) :=
      mul_le_mul_of_nonneg_left fieldControl chartBoundNonnegative
    _ = _ := by ring

end EulerNonuniqueness.Section6
