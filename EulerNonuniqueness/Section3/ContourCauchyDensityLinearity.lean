import EulerNonuniqueness.Section3.ContourCauchyBilinearTaylor
import EulerNonuniqueness.Section3.ContourVelocityHolderDerivative

open MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

theorem holder_real_smul_eq_complex (scalar : ℝ) (data : PeriodicHolderHalf) :
    scalar • data = (scalar : ℂ) • data := by
  apply PeriodicHolderHalf.ext_value
  intro label
  rfl

theorem c1Holder_real_smul_eq_complex (scalar : ℝ) (data : PeriodicC1HolderHalf) :
    scalar • data = (scalar : ℂ) • data := by
  apply PeriodicC1HolderHalf.ext_value
  intro label
  rfl

theorem contourCauchyDirectionalDerivative_smul_density
    (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℂ) :
    contourCauchyDirectionalDerivative data direction (scalar • density) =
      scalar • contourCauchyDirectionalDerivative data direction density := by
  apply PeriodicHolderHalf.ext_value
  intro target
  rw [contourCauchyDirectionalDerivative_value data direction (scalar • density) small]
  change (∫ source in (target - Real.pi)..(target + Real.pi),
      (scalar * density.val.1 source - scalar * density.val.1 target) *
        contourCauchyKernelVariation data direction target source) =
    scalar * (contourCauchyDirectionalDerivative data direction density).val.1 target
  rw [contourCauchyDirectionalDerivative_value data direction density small,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro source _
  dsimp only
  ring

theorem contourCauchyDirectionalDerivative_real_smul_direction
    (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourCauchyDirectionalDerivative data (scalar • direction) density =
      scalar • contourCauchyDirectionalDerivative data direction density := by
  rw [c1Holder_real_smul_eq_complex, contourCauchyDirectionalDerivative_smul data direction density small,
    ← holder_real_smul_eq_complex]

theorem contourCauchyDirectionalDerivative_real_smul_density
    (data direction : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourCauchyDirectionalDerivative data direction (scalar • density) =
      scalar • contourCauchyDirectionalDerivative data direction density := by
  rw [holder_real_smul_eq_complex, contourCauchyDirectionalDerivative_smul_density data direction density small,
    ← holder_real_smul_eq_complex]

theorem contourCauchySecondVariation_real_smul_left
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourCauchySecondVariation data (scalar • first) second density =
      scalar • contourCauchySecondVariation data first second density := by
  rw [c1Holder_real_smul_eq_complex, contourCauchySecondVariation_smul_left data first second density small,
    ← holder_real_smul_eq_complex]

theorem contourCauchySecondVariation_real_smul_right
    (data first second : PeriodicC1HolderHalf) (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourCauchySecondVariation data first (scalar • second) density =
      scalar • contourCauchySecondVariation data first second density := by
  rw [c1Holder_real_smul_eq_complex, contourCauchySecondVariation_smul_right data first second density small,
    ← holder_real_smul_eq_complex]

theorem extendedContourCauchy_real_smul_density (data : PeriodicC1HolderHalf)
    (density : PeriodicHolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    extendedContourCauchy data (scalar • density) = scalar • extendedContourCauchy data density := by
  rw [extendedContourCauchy_eq _ _ small, extendedContourCauchy_eq _ _ small]
  exact (contourCauchyOperatorCLM data small).map_smul scalar density

end

end EulerNonuniqueness.Paper
