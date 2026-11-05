import EulerNonuniqueness.Section3.ContourCauchyDensityLinearity

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem contourCauchyDirectionalDerivative_add_density
    (data direction : PeriodicC1HolderHalf) (first second : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchyDirectionalDerivative data direction (first + second) =
      contourCauchyDirectionalDerivative data direction first +
        contourCauchyDirectionalDerivative data direction second := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchyDirectionalDerivative data direction (first + second)).val.1 target =
    (contourCauchyDirectionalDerivative data direction first).val.1 target +
      (contourCauchyDirectionalDerivative data direction second).val.1 target
  rw [contourCauchyDirectionalDerivative_value data direction (first + second) small,
    contourCauchyDirectionalDerivative_value data direction first small,
    contourCauchyDirectionalDerivative_value data direction second small,
    ← intervalIntegral.integral_add
      (contourCauchyKernelVariation_density_integrable data direction first
        (small.trans_le (min_le_right _ _)) target)
      (contourCauchyKernelVariation_density_integrable data direction second
        (small.trans_le (min_le_right _ _)) target)]
  apply intervalIntegral.integral_congr
  intro source _
  change (first.val.1 source + second.val.1 source -
      (first.val.1 target + second.val.1 target)) *
      contourCauchyKernelVariation data direction target source = _
  dsimp only
  ring

theorem contourCauchySecondVariation_add_right
    (data first second third : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariation data first (second + third) density =
      contourCauchySecondVariation data first second density +
        contourCauchySecondVariation data first third density := by
  rw [contourCauchySecondVariation_symm data first (second + third) density small,
    contourCauchySecondVariation_add_left data second third first density small,
    contourCauchySecondVariation_symm data second first density small,
    contourCauchySecondVariation_symm data third first density small]

end

end EulerNonuniqueness.Paper
