import EulerNonuniqueness.Section3.ContourVelocityQuadraticGraph

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance velocityCubicTaylorHolderRealSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance velocityCubicTaylorC1RealSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

def contourVelocityQuadratic (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf :=
  ⟨contourVelocityAmbientQuadratic data increment, contourVelocityAmbientQuadratic_mem data increment small⟩

def contourVelocityDerivative (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  closedSubmoduleDerivative (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient)
    periodicC1HolderGraph periodicC1HolderGraph_isClosed (function := extendedContourVelocity)
    (derivative := contourVelocityAmbientDerivativeCLM data near small) (point := data)
    (hasFDerivAt_contourVelocityAmbient data near small)

theorem hasFDerivAt_contourVelocityDerivative (data : PeriodicC1HolderHalf) {radius : ℝ}
    (near : ‖data - standardCircleBanach‖ < radius)
    (small : radius < min 1 (2 / (3 * Real.pi))) :
    HasFDerivAt extendedContourVelocity (contourVelocityDerivative data near small) data := by
  exact hasFDerivAt_closedSubmodule (E := PeriodicC1HolderHalf) (F := C1HolderGraphAmbient)
    periodicC1HolderGraph periodicC1HolderGraph_isClosed (function := extendedContourVelocity)
    (derivative := contourVelocityAmbientDerivativeCLM data near small) (point := data)
    (hasFDerivAt_contourVelocityAmbient data near small)

theorem contourVelocityQuadratic_value (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (label : ℝ) :
    (contourVelocityQuadratic data increment small).val.1 label =
      (contourVelocityHolderQuadratic data increment).val.1 label := rfl

theorem contourVelocityQuadratic_tangent (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) :
    (contourVelocityQuadratic data increment small).val.2 =
      contourVelocityTangentQuadratic data increment := rfl

theorem contourVelocityQuadratic_real_smul (data increment : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < min 1 (2 / (3 * Real.pi))) (scalar : ℝ) :
    contourVelocityQuadratic data (scalar • increment) small =
      scalar ^ 2 • contourVelocityQuadratic data increment small := by
  apply Subtype.ext
  exact contourVelocityAmbientQuadratic_real_smul data increment small scalar

theorem contourVelocity_cubic_taylor_bound (data increment : PeriodicC1HolderHalf)
    {innerRadius outerRadius : ℝ} (nonnegative : 0 ≤ innerRadius)
    (gap : innerRadius < outerRadius) (small : outerRadius < min 1 (2 / (3 * Real.pi)))
    (nearby : ‖data - standardCircleBanach‖ ≤ innerRadius)
    (increment_small : ‖increment‖ ≤ (outerRadius - innerRadius) / 4)
    (inverse_small : ‖increment‖ ≤ (1 - outerRadius) / 2) (increment_bound : ‖increment‖ ≤ 1) :
    ‖extendedContourVelocity (data + increment) - extendedContourVelocity data -
      fderiv ℝ extendedContourVelocity data increment -
      contourVelocityQuadratic data increment ((nearby.trans_lt gap).trans small)‖ ≤
      contourVelocityAmbientCubicBound data innerRadius outerRadius * ‖increment‖ ^ 3 := by
  have derivative : fderiv ℝ extendedContourVelocity data =
      contourVelocityDerivative data (nearby.trans_lt gap) small := by
    exact HasFDerivAt.fderiv (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := PeriodicC1HolderHalf)
      (hasFDerivAt_contourVelocityDerivative data (nearby.trans_lt gap) small)
  rw [derivative]
  change ‖(extendedContourVelocity (data + increment)).val - (extendedContourVelocity data).val -
    contourVelocityAmbientDerivativeCLM data (nearby.trans_lt gap) small increment -
    contourVelocityAmbientQuadratic data increment‖ ≤ _
  exact contourVelocityAmbient_cubic_taylor_bound data increment nonnegative gap small nearby
    increment_small inverse_small increment_bound

end

end EulerNonuniqueness.Paper
