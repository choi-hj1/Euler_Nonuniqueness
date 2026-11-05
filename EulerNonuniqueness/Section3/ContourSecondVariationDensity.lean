import EulerNonuniqueness.Section3.ContourSecondVariationBilinear

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

theorem contourCauchySecondVariation_add_density (data first second : PeriodicC1HolderHalf)
    (initial final : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    contourCauchySecondVariation data first second (initial + final) =
      contourCauchySecondVariation data first second initial + contourCauchySecondVariation data first second final := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchySecondVariation data first second (initial + final)).val.1 target =
    (contourCauchySecondVariation data first second initial).val.1 target +
      (contourCauchySecondVariation data first second final).val.1 target
  rw [contourCauchySecondVariation_value data first second (initial + final) small,
    contourCauchySecondVariation_value data first second initial small,
    contourCauchySecondVariation_value data first second final small]
  unfold contourCauchyQuadraticIntegral
  rw [← mul_add, ← intervalIntegral.integral_add
    (contourCauchyQuadraticIntegral_integrable data first second initial (small.trans_le (min_le_right _ _)) target)
    (contourCauchyQuadraticIntegral_integrable data first second final (small.trans_le (min_le_right _ _)) target)]
  congr 1
  apply intervalIntegral.integral_congr
  intro source _
  change (initial.val.1 source + final.val.1 source - (initial.val.1 target + final.val.1 target)) * _ = _
  ring

theorem contourCauchySecondVariation_smul_density (data first second : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℂ) :
    contourCauchySecondVariation data first second (scalar • density) =
      scalar • contourCauchySecondVariation data first second density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  change (contourCauchySecondVariation data first second (scalar • density)).val.1 target =
    scalar * (contourCauchySecondVariation data first second density).val.1 target
  rw [contourCauchySecondVariation_value data first second (scalar • density) small,
    contourCauchySecondVariation_value data first second density small]
  unfold contourCauchyQuadraticIntegral
  have identity : (fun source => ((scalar • density).val.1 source - (scalar • density).val.1 target) *
      contourCauchyKernelQuadratic data first second target source) =
      (fun source => scalar * ((density.val.1 source - density.val.1 target) *
        contourCauchyKernelQuadratic data first second target source)) := by
    funext source
    change (scalar * density.val.1 source - scalar * density.val.1 target) * _ = _
    ring
  rw [identity, intervalIntegral.integral_const_mul]
  ring

end

end EulerNonuniqueness.Paper
