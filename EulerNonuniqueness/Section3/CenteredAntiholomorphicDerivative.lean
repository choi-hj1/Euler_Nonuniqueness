import EulerNonuniqueness.Section3.CenteredAntiholomorphicAnalytic
import EulerNonuniqueness.General.WeightedFieldEquivariance

namespace EulerNonuniqueness.Paper

noncomputable section

open Filter
open scoped Topology

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem centeredAntiholomorphicForcing_derivative_normalized_shift (degree : ℕ)
    (offset : ℝ) (direction : PeriodicC1HolderHalf) :
    normalizedContourShift offset
      (fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach direction) =
    ((standardCircle offset)⁻¹ ^ (degree + 2)) •
      (fderiv ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach
        (normalizedContourShift offset direction)) := by
  let weight : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
    c1ProductCLM (c1Constant ((standardCircle offset)⁻¹ ^ (degree + 2)))
  have weight_apply (current : PeriodicC1HolderHalf) :
      weight current = ((standardCircle offset)⁻¹ ^ (degree + 2)) • current := by
    apply PeriodicC1HolderHalf.ext_value
    intro label
    rfl
  have equivariant : (fun current => normalizedContourShiftCLM offset (centeredAntiholomorphicForcing degree current)) =ᶠ[𝓝 standardCircleBanach]
      (fun current => weight (centeredAntiholomorphicForcing degree (normalizedContourShiftCLM offset current))) := by
    filter_upwards [] with current
    simpa only [normalizedContourShiftCLM_apply, weight_apply] using
      centeredAntiholomorphicForcing_normalized_shift degree current offset
  have differentiable : DifferentiableAt ℝ (centeredAntiholomorphicForcing degree) standardCircleBanach :=
    (centeredAntiholomorphicForcing_analyticAt degree standardCircleBanach).differentiableAt
  have identity := EulerNonuniqueness.General.weighted_field_derivative_intertwines
    (Space := PeriodicC1HolderHalf) (centeredAntiholomorphicForcing degree)
    (normalizedContourShiftCLM offset) (normalizedContourShiftCLM offset) weight standardCircleBanach
    (normalizedContourShift_circle offset) differentiable equivariant
  have pointwise := congrArg (fun operator : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf => operator direction) identity
  simpa only [ContinuousLinearMap.comp_apply, normalizedContourShiftCLM_apply, weight_apply] using pointwise

end

end EulerNonuniqueness.Paper
