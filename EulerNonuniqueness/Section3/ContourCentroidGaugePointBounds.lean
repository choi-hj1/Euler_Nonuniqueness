import EulerNonuniqueness.Section3.ContourCentroidGaugeRegularity

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

local instance centroidPointBoundHolderSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance centroidPointBoundC1Space : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph
local instance centroidPointBoundDerivativeGroup : NormedAddCommGroup (PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := PeriodicC1HolderHalf) (F := ℂ) (σ₁₂ := RingHom.id ℝ)

theorem contourCentroidGaugeProjection_apply_norm_bound (data direction : PeriodicC1HolderHalf)
    {constant bound : ℝ} (constantNonnegative : 0 ≤ constant)
    (derivativeBound : ‖fderiv ℝ contourCentroidFunctional data‖ ≤ constant) (directionBound : ‖direction‖ ≤ bound) :
    ‖contourCentroidGaugeProjection data direction‖ ≤ (1 + constant) * bound := by
  have derivativeApplication : ‖(fderiv ℝ contourCentroidFunctional data) direction‖ ≤ constant * bound :=
    ((fderiv ℝ contourCentroidFunctional data).le_opNorm direction).trans
      (mul_le_mul derivativeBound directionBound (norm_nonneg direction) constantNonnegative)
  have constantApplication := (c1Constant_norm_bound ((fderiv ℝ contourCentroidFunctional data) direction)).trans derivativeApplication
  rw [contourCentroidGaugeProjection_apply]
  exact ((norm_sub_le direction (c1Constant ((fderiv ℝ contourCentroidFunctional data) direction))).trans
    (add_le_add directionBound constantApplication)).trans_eq (by ring)

end EulerNonuniqueness.Paper
