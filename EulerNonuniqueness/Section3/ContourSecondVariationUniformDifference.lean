import EulerNonuniqueness.Section3.ContourSecondVariationMixedDifference

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondVariationBilinearHolderComplexSpace
  secondVariationBilinearC1ComplexSpace secondVariationBilinearOperatorGroup
  secondVariationBilinearOperatorSpace

theorem contourCauchySecondVariation_uniform_mixed_difference_bound
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    {parameter : ℂ} (nonzero : parameter ≠ 0)
    (sumSmall : ‖parameter • (first + second)‖ ≤ (outerRadius - innerRadius) / 4)
    (firstSmall : ‖parameter • first‖ ≤ (outerRadius - innerRadius) / 4)
    (secondSmall : ‖parameter • second‖ ≤ (outerRadius - innerRadius) / 4) :
    ‖(parameter ^ 2)⁻¹ •
        (extendedContourCauchy (data + parameter • (first + second)) density -
          extendedContourCauchy (data + parameter • first) density -
          extendedContourCauchy (data + parameter • second) density +
          extendedContourCauchy data density) -
        contourCauchySecondVariation data first second density‖ ≤
      (16 * (contourCauchyUniformOperatorConstant outerRadius * ‖density‖) /
        (outerRadius - innerRadius) ^ 3) * ‖parameter‖ *
          (‖first + second‖ ^ 3 + ‖first‖ ^ 3 + ‖second‖ ^ 3) := by
  obtain ⟨middle, innerMiddle, middleOuter⟩ := exists_between gap
  have localSmall : (outerRadius - innerRadius) / 4 ≤
      (outerRadius - ‖data - standardCircleBanach‖) / 4 := by linarith
  have estimate := contourCauchySecondVariation_mixed_difference_bound data first second density
    (near.trans_lt innerMiddle) middleOuter small nonzero
    (sumSmall.trans localSmall) (firstSmall.trans localSmall) (secondSmall.trans localSmall)
  apply estimate.trans
  have constantNonnegative := contourCauchyUniformOperatorConstant_nonneg
    ((norm_nonneg _).trans (near.trans gap.le)) small
  have gapPositive : 0 < outerRadius - innerRadius := sub_pos.mpr gap
  gcongr

end

end EulerNonuniqueness.Paper
