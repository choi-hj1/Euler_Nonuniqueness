import EulerNonuniqueness.Section3.NearCircleSpacetimeDifferentiation
import EulerNonuniqueness.Section3.SpacetimeContourFlux

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance nearCircleSpacetimeReynoldsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance nearCircleSpacetimeReynoldsC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem nearCircleInterior_hasDerivAt_spacetime_Reynolds
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
      ((∫ position in nearCircleInterior (shape time) (small time), derivative (time, position) (1, 0)) +
        ∫ label in (-Real.pi)..Real.pi, function (time, (shape time).val.1 label) *
          contourAreaPair ((velocity time).val.1 label) ((shape time).val.2.val.1 label)) time := by
  have result := nearCircleInterior_hasDerivAt_spacetime_integral shape velocity shape_continuous
    velocity_continuous small time radius radius_positive equation function derivative function_continuous
    derivative_continuous function_derivative
  have flux_identity := integral_spacetimeContourReynolds_variation function derivative function_continuous
    derivative_continuous function_derivative time
    (fun label => (shape time).val.1 label) (fun label => (shape time).val.2.val.1 label)
    (fun label => (velocity time).val.1 label) (fun label => (velocity time).val.2.val.1 label)
    ((continuous_contour_value_joint shape shape_continuous).comp (continuous_const.prodMk continuous_id))
    ((continuous_contour_tangent_joint shape shape_continuous).comp (continuous_const.prodMk continuous_id))
    ((continuous_contour_value_joint velocity velocity_continuous).comp (continuous_const.prodMk continuous_id))
    ((continuous_contour_tangent_joint velocity velocity_continuous).comp (continuous_const.prodMk continuous_id))
    (PeriodicC1HolderHalf.hasDerivAt (shape time)) (PeriodicC1HolderHalf.hasDerivAt (velocity time))
    (-Real.pi) Real.pi
    (by convert PeriodicC1HolderHalf.periodic (shape time) (-Real.pi) using 1 <;> congr 1 <;> ring)
    (by convert PeriodicC1HolderHalf.periodic (velocity time) (-Real.pi) using 1 <;> congr 1 <;> ring)
  rw [flux_identity] at result
  have temporal_continuous : Continuous (fun position => derivative (time, position) (1, (0 : ℂ))) :=
    (derivative_continuous.comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have temporal_identity :
      (∫ position in nearCircleInterior (shape time) (small time), derivative (time, position) (1, 0)) =
      ∫ label in (-Real.pi)..Real.pi, ∫ scale in (0 : ℝ)..1,
        scale * derivative (time, scale • (shape time).val.1 label) (1, 0) *
          contourAreaPair ((shape time).val.1 label) ((shape time).val.2.val.1 label) := by
    rw [integral_nearCircleInterior_radial_flux (shape time) (small time)
      (fun position => derivative (time, position) (1, 0)) temporal_continuous]
    apply intervalIntegral.integral_congr
    intro label _
    change contourAreaPair ((shape time).val.1 label) ((shape time).val.2.val.1 label) *
      (∫ scale in (0 : ℝ)..1, scale * derivative (time, scale • (shape time).val.1 label) (1, 0)) = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro scale _
    ring
  rw [temporal_identity]
  exact result

end

end EulerNonuniqueness.Paper
