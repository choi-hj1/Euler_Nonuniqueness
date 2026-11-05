import EulerNonuniqueness.Section3.AffinePatchReynolds
import EulerNonuniqueness.Section3.NearCircleSpacetimeReynolds

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance affineSpacetimeHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance affineSpacetimeC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem affinePatchDomain_hasDerivAt_spacetime_Reynolds
    (center : ℂ) {scale : ℝ} (positive : 0 < scale)
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shape_continuous : Continuous shape) (velocity_continuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time radius : ℝ) (radius_positive : 0 < radius)
    (equation : ∀ parameter ∈ Metric.ball time radius, HasDerivAt shape (velocity parameter) parameter)
    (function : ℝ × ℂ → ℝ) (derivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ point, HasFDerivAt function (derivative point) point) :
    HasDerivAt (fun parameter => ∫ position in affinePatchDomain center scale (shape parameter) (small parameter),
      function (parameter, position))
      ((∫ position in affinePatchDomain center scale (shape time) (small time), derivative (time, position) (1, 0)) +
        ∫ label in (-Real.pi)..Real.pi, function (time, center + scale • (shape time).val.1 label) *
          contourAreaPair (scale • (velocity time).val.1 label) (scale • (shape time).val.2.val.1 label)) time := by
  let affine : ℝ × ℂ → ℝ × ℂ := fun pair => (pair.1, center + scale • pair.2)
  let linear : (ℝ × ℂ) →L[ℝ] (ℝ × ℂ) :=
    (ContinuousLinearMap.fst ℝ ℝ ℂ).prod (scale • ContinuousLinearMap.snd ℝ ℝ ℂ)
  have affine_continuous : Continuous affine :=
    continuous_fst.prodMk (continuous_const.add (continuous_const.smul continuous_snd))
  have affine_derivative (point : ℝ × ℂ) : HasFDerivAt affine linear point := by
    simpa only [zero_add] using (ContinuousLinearMap.fst ℝ ℝ ℂ).hasFDerivAt.prodMk
      ((hasFDerivAt_const (𝕜 := ℝ) center point).add
        ((ContinuousLinearMap.snd ℝ ℝ ℂ).hasFDerivAt.const_smul scale))
  let pulledDerivative : ℝ × ℂ → (ℝ × ℂ) →L[ℝ] ℝ := fun point =>
    (derivative (affine point)).comp linear
  have pulled_continuous : Continuous pulledDerivative :=
    (derivative_continuous.comp affine_continuous).clm_comp continuous_const
  have result := nearCircleInterior_hasDerivAt_spacetime_Reynolds shape velocity shape_continuous velocity_continuous
    small time radius radius_positive equation (function ∘ affine) pulledDerivative
    (function_continuous.comp affine_continuous) pulled_continuous
    (fun point => (function_derivative _).comp point (affine_derivative point))
  have multiplied := result.const_mul (scale ^ 2)
  have integral_identity :
      (fun parameter => ∫ position in affinePatchDomain center scale (shape parameter) (small parameter), function (parameter, position)) =
      (fun parameter => scale ^ 2 * ∫ position in nearCircleInterior (shape parameter) (small parameter),
        (function ∘ affine) (parameter, position)) := by
    funext parameter
    exact integral_affinePatchDomain center positive (shape parameter) (small parameter)
      (fun position => function (parameter, position))
  rw [integral_identity]
  convert multiplied using 1
  rw [mul_add]
  congr 1
  · rw [integral_affinePatchDomain center positive (shape time) (small time)
      (fun position => derivative (time, position) (1, 0))]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => by
      simp [pulledDerivative, affine, linear]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro label _
    dsimp only [Function.comp_apply, affine]
    rw [contourAreaPair_real_scaling]
    ring

end

end EulerNonuniqueness.Paper
