import EulerNonuniqueness.Section3.NearCircleReynolds
import EulerNonuniqueness.Section3.SpacetimeContourDifferentiation

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance nearCircleSpacetimeHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance nearCircleSpacetimeC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem nearCircleInterior_hasDerivAt_spacetime_integral
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shape_continuous : Continuous shape) (velocity_continuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time radius : ℝ) (radius_positive : 0 < radius)
    (equation : ∀ parameter ∈ Metric.ball time radius, HasDerivAt shape (velocity parameter) parameter)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter),
      function (parameter, position))
      (∫ label in (-Real.pi)..Real.pi, ∫ scale in (0 : ℝ)..1,
        scale * (derivative (time, scale • (shape time).val.1 label)
          (1, scale • (velocity time).val.1 label) *
            contourAreaPair ((shape time).val.1 label) ((shape time).val.2.val.1 label) +
          function (time, scale • (shape time).val.1 label) *
            (contourAreaPair ((velocity time).val.1 label) ((shape time).val.2.val.1 label) +
              contourAreaPair ((shape time).val.1 label) ((velocity time).val.2.val.1 label)))) time := by
  have integral_identity :
      (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter), function (parameter, position)) =
      (fun parameter => ∫ label in (-Real.pi)..Real.pi, ∫ scale in (0 : ℝ)..1,
        scale * function (parameter, scale • (shape parameter).val.1 label) *
          contourAreaPair ((shape parameter).val.1 label) ((shape parameter).val.2.val.1 label)) := by
    funext parameter
    rw [integral_nearCircleInterior_radial_flux (shape parameter) (small parameter)
      (fun position => function (parameter, position))
      (function_continuous.comp (continuous_const.prodMk continuous_id))]
    apply intervalIntegral.integral_congr
    intro label _
    change contourAreaPair ((shape parameter).val.1 label) ((shape parameter).val.2.val.1 label) *
      (∫ scale in (0 : ℝ)..1, scale * function (parameter, scale • (shape parameter).val.1 label)) = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro scale _
    ring
  rw [integral_identity]
  exact hasDerivAt_spacetimeMaterialRadialIntegral function derivative function_continuous derivative_continuous
    function_derivative
    (fun parameter label => (shape parameter).val.1 label)
    (fun parameter label => (shape parameter).val.2.val.1 label)
    (fun parameter label => (velocity parameter).val.1 label)
    (fun parameter label => (velocity parameter).val.2.val.1 label)
    (continuous_contour_value_joint shape shape_continuous)
    (continuous_contour_tangent_joint shape shape_continuous)
    (continuous_contour_value_joint velocity velocity_continuous)
    (continuous_contour_tangent_joint velocity velocity_continuous)
    time radius (-Real.pi) Real.pi radius_positive
    (fun parameter inside label => hasDerivAt_contour_value (equation parameter inside) label)
    (fun parameter inside label => hasDerivAt_contour_tangent (equation parameter inside) label)

end

end EulerNonuniqueness.Paper
