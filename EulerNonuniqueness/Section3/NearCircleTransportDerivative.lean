import EulerNonuniqueness.Section3.NearCircleReynolds
import EulerNonuniqueness.Section3.ContourBiotSavartAdvection

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance nearCircleTransportHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance nearCircleTransportC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem nearCircleInterior_hasDerivAt_advection
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shape_continuous : Continuous shape) (velocity_continuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time radius : ℝ) (radius_positive : 0 < radius)
    (equation : ∀ parameter ∈ Metric.ball time radius, HasDerivAt shape (velocity parameter) parameter)
    {source : Vorticity} (integrable : Integrable source)
    (membership : MemLp source (ENNReal.ofReal (4 : ℝ)) volume)
    (material_boundary : ∀ label, (velocity time).val.1 label = biotSavart source ((shape time).val.1 label))
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position in nearCircleInterior (shape parameter) (small parameter), function position)
      (∫ position in nearCircleInterior (shape time) (small time), derivative position (biotSavart source position)) time := by
  have reynolds := nearCircleInterior_hasDerivAt_integral shape velocity shape_continuous velocity_continuous
    small time radius radius_positive equation function derivative function_continuous derivative_continuous function_derivative
  have flux_identity :
      (∫ position in nearCircleInterior (shape time) (small time), derivative position (biotSavart source position)) =
      ∫ label in (-Real.pi)..Real.pi, function ((shape time).val.1 label) *
        contourAreaPair ((velocity time).val.1 label) ((shape time).val.2.val.1 label) := by
    rw [integral_nearCircleInterior_biotSavart_advection (shape time) (small time) function derivative
      function_continuous derivative_continuous function_derivative integrable membership]
    apply intervalIntegral.integral_congr
    intro label _
    dsimp only
    rw [material_boundary label]
  rw [flux_identity]
  exact reynolds

end

end EulerNonuniqueness.Paper
