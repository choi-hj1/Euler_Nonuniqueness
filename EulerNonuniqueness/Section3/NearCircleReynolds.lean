import EulerNonuniqueness.Section3.ContourReynolds
import EulerNonuniqueness.Section3.C1ContourEvaluation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance nearCircleReynoldsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance nearCircleReynoldsC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem nearCircleInterior_hasDerivAt_integral
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shape_continuous : Continuous shape) (velocity_continuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time radius : ℝ) (radius_positive : 0 < radius)
    (equation : ∀ parameter ∈ Metric.ball time radius, HasDerivAt shape (velocity parameter) parameter)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter), function position)
      (∫ label in (-Real.pi)..Real.pi, function ((shape time).val.1 label) *
        contourAreaPair ((velocity time).val.1 label) ((shape time).val.2.val.1 label)) time := by
  have integral_identity :
      (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter), function position) =
      (fun parameter => ∫ label in (-Real.pi)..Real.pi, ∫ scale in (0 : ℝ)..1,
        scale * function (scale • (shape parameter).val.1 label) *
          contourAreaPair ((shape parameter).val.1 label) ((shape parameter).val.2.val.1 label)) := by
    funext parameter
    rw [integral_nearCircleInterior_radial_flux (shape parameter) (small parameter) function function_continuous]
    apply intervalIntegral.integral_congr
    intro label _
    change contourAreaPair ((shape parameter).val.1 label) ((shape parameter).val.2.val.1 label) *
      (∫ scale in (0 : ℝ)..1, scale * function (scale • (shape parameter).val.1 label)) = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro scale _
    ring
  rw [integral_identity]
  apply hasDerivAt_materialRadialFlux function derivative function_continuous derivative_continuous function_derivative
    (fun parameter label => (shape parameter).val.1 label)
    (fun parameter label => (shape parameter).val.2.val.1 label)
    (fun parameter label => (velocity parameter).val.1 label)
    (fun parameter label => (velocity parameter).val.2.val.1 label)
    (continuous_contour_value_joint shape shape_continuous)
    (continuous_contour_tangent_joint shape shape_continuous)
    (continuous_contour_value_joint velocity velocity_continuous)
    (continuous_contour_tangent_joint velocity velocity_continuous)
    time radius radius_positive
    (fun parameter inside label => hasDerivAt_contour_value (equation parameter inside) label)
    (fun parameter inside label => hasDerivAt_contour_tangent (equation parameter inside) label)
    (-Real.pi) Real.pi
    (PeriodicC1HolderHalf.hasDerivAt (shape time))
    (PeriodicC1HolderHalf.hasDerivAt (velocity time))
  · convert PeriodicC1HolderHalf.periodic (shape time) (-Real.pi) using 1 <;> congr 1 <;> ring
  · convert PeriodicC1HolderHalf.periodic (velocity time) (-Real.pi) using 1 <;> congr 1 <;> ring

end

end EulerNonuniqueness.Paper
