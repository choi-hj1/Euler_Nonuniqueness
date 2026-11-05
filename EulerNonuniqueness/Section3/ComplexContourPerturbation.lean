import EulerNonuniqueness.Section3.ComplexHolderInstances
import EulerNonuniqueness.Section3.ContourKernelVariation

open Set
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

theorem complexContourPerturbation_distance (data direction : PeriodicC1HolderHalf) (parameter : ℂ) :
    ‖data + parameter • direction - standardCircleBanach‖ ≤
      ‖data - standardCircleBanach‖ + ‖parameter‖ * ‖direction‖ := by
  have identity : data + parameter • direction - standardCircleBanach =
      (data - standardCircleBanach) + parameter • direction := by abel
  rw [identity]
  exact (norm_add_le (data - standardCircleBanach) (parameter • direction)).trans_eq
    (by rw [norm_smul parameter direction])

theorem complexContourPerturbation_near (data direction : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius) {parameter : ℂ}
    (small : ‖parameter‖ < (radius - ‖data - standardCircleBanach‖) / (‖direction‖ + 1)) :
    ‖data + parameter • direction - standardCircleBanach‖ < radius := by
  have denominator_positive : 0 < ‖direction‖ + 1 := by positivity
  have bound := (lt_div_iff₀ denominator_positive).mp small
  exact (complexContourPerturbation_distance data direction parameter).trans_lt
    (by nlinarith [norm_nonneg parameter])

theorem contourCauchyKernel_hasDerivAt_complex_parameter (data direction : PeriodicC1HolderHalf)
    (parameter : ℂ) {target source : ℝ}
    (separated : (data + parameter • direction).val.1 target - (data + parameter • direction).val.1 source ≠ 0) :
    HasDerivAt (fun current : ℂ => contourCauchyKernel (data + current • direction).val.1
      (data + current • direction).val.2.val.1 target source)
      (contourCauchyKernelVariation (data + parameter • direction) direction target source) parameter := by
  have numerator := (hasDerivAt_const parameter (data.val.2.val.1 source)).add
    ((hasDerivAt_id parameter).mul_const (direction.val.2.val.1 source))
  have denominator := ((hasDerivAt_const parameter (data.val.1 target)).add
      ((hasDerivAt_id parameter).mul_const (direction.val.1 target))).sub
    ((hasDerivAt_const parameter (data.val.1 source)).add
      ((hasDerivAt_id parameter).mul_const (direction.val.1 source)))
  have denominator_ne : data.val.1 target + parameter * direction.val.1 target -
      (data.val.1 source + parameter * direction.val.1 source) ≠ 0 := separated
  have result := numerator.div denominator denominator_ne
  convert result using 1
  simp only [zero_add, one_mul, id_eq, contourCauchyKernelVariation]
  change direction.val.2.val.1 source /
        (data.val.1 target + parameter * direction.val.1 target - (data.val.1 source + parameter * direction.val.1 source)) -
      (data.val.2.val.1 source + parameter * direction.val.2.val.1 source) *
        (direction.val.1 target - direction.val.1 source) /
        (data.val.1 target + parameter * direction.val.1 target - (data.val.1 source + parameter * direction.val.1 source)) ^ 2 = _
  field_simp
  ring

end

end EulerNonuniqueness.Paper
