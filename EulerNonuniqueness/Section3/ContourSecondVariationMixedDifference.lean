import EulerNonuniqueness.Section3.ContourCauchyCubicTaylor
import EulerNonuniqueness.Section3.ContourSecondVariationBilinear
import EulerNonuniqueness.General.SecondJetMixedDifference

namespace EulerNonuniqueness.Paper

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] secondVariationBilinearHolderComplexSpace
  secondVariationBilinearC1ComplexSpace secondVariationBilinearOperatorGroup
  secondVariationBilinearOperatorSpace

theorem contourCauchySecondVariation_mixed_difference_bound
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    {innerRadius outerRadius : ℝ} (near : ‖data - standardCircleBanach‖ < innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    {parameter : ℂ} (nonzero : parameter ≠ 0)
    (sumSmall : ‖parameter • (first + second)‖ ≤
      (outerRadius - ‖data - standardCircleBanach‖) / 4)
    (firstSmall : ‖parameter • first‖ ≤
      (outerRadius - ‖data - standardCircleBanach‖) / 4)
    (secondSmall : ‖parameter • second‖ ≤
      (outerRadius - ‖data - standardCircleBanach‖) / 4) :
    ‖(parameter ^ 2)⁻¹ •
        (extendedContourCauchy (data + parameter • (first + second)) density -
          extendedContourCauchy (data + parameter • first) density -
          extendedContourCauchy (data + parameter • second) density +
          extendedContourCauchy data density) -
        contourCauchySecondVariation data first second density‖ ≤
      (16 * (contourCauchyUniformOperatorConstant outerRadius * ‖density‖) /
        (outerRadius - ‖data - standardCircleBanach‖) ^ 3) * ‖parameter‖ *
          (‖first + second‖ ^ 3 + ‖first‖ ^ 3 + ‖second‖ ^ 3) := by
  let linear := contourCauchyDerivativeCLM data density (near.trans gap) small
  let bilinear := contourCauchySecondVariationCLM data density near gap small
  have symmetric : bilinear second first = bilinear first second :=
    contourCauchySecondVariation_symm data second first density (near.trans (gap.trans small))
  have bound (increment : PeriodicC1HolderHalf)
      (incrementSmall : ‖increment‖ ≤ (outerRadius - ‖data - standardCircleBanach‖) / 4) :
      ‖EulerNonuniqueness.General.complexSecondJetError
        (fun current => extendedContourCauchy current density) linear bilinear data increment‖ ≤
        (16 * (contourCauchyUniformOperatorConstant outerRadius * ‖density‖) /
          (outerRadius - ‖data - standardCircleBanach‖) ^ 3) * ‖increment‖ ^ 3 := by
    exact contourCauchy_cubic_taylor_bound data increment density (near.trans gap) small incrementSmall
  have value : bilinear first second = contourCauchySecondVariation data first second density :=
    contourCauchySecondVariationCLM_apply data first second density near gap small
  with_reducible
    have actual := EulerNonuniqueness.General.norm_secondJet_scaled_mixed_difference_le
      (fun current => extendedContourCauchy current density) linear bilinear data first second
      nonzero symmetric (bound _ sumSmall) (bound _ firstSmall) (bound _ secondSmall)
    rw [value] at actual
    exact actual

end

end EulerNonuniqueness.Paper
