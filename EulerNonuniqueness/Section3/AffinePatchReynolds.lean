import EulerNonuniqueness.Section3.AffinePatchDomain
import EulerNonuniqueness.Section3.NearCircleReynolds

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000

local instance affinePatchReynoldsHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf :=
  Submodule.normedSpace periodicHolderGraph
local instance affinePatchReynoldsC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf :=
  Submodule.normedSpace periodicC1HolderGraph

theorem contourAreaPair_real_scaling (scale : ℝ) (first second : ℂ) :
    contourAreaPair (scale • first) (scale • second) = scale ^ 2 * contourAreaPair first second := by
  simp only [contourAreaPair_coordinates, Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

theorem affinePatchDomain_hasDerivAt_integral
    (center : ℂ) {scale : ℝ} (positive : 0 < scale)
    (shape velocity : ℝ → PeriodicC1HolderHalf)
    (shape_continuous : Continuous shape) (velocity_continuous : Continuous velocity)
    (small : ∀ parameter, ‖shape parameter - standardCircleBanach‖ < 1 / 3)
    (time radius : ℝ) (radius_positive : 0 < radius)
    (equation : ∀ parameter ∈ Metric.ball time radius, HasDerivAt shape (velocity parameter) parameter)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position) :
    HasDerivAt (fun parameter => ∫ position in affinePatchDomain center scale (shape parameter) (small parameter), function position)
      (∫ label in (-Real.pi)..Real.pi, function (center + scale • (shape time).val.1 label) *
        contourAreaPair (scale • (velocity time).val.1 label) (scale • (shape time).val.2.val.1 label)) time := by
  let affine : ℂ → ℂ := fun position => center + scale • position
  have affine_continuous : Continuous affine := continuous_const.add (continuous_const.smul continuous_id)
  have affine_derivative (position : ℂ) : HasFDerivAt affine (scale • ContinuousLinearMap.id ℝ ℂ) position := by
    simpa only [zero_add] using (hasFDerivAt_const (𝕜 := ℝ) center position).add
      ((hasFDerivAt_id (𝕜 := ℝ) position).const_smul scale)
  let pulledDerivative : ℂ → ℂ →L[ℝ] ℝ := fun position =>
    (derivative (affine position)).comp (scale • ContinuousLinearMap.id ℝ ℂ)
  have pulledDerivative_continuous : Continuous pulledDerivative :=
    (derivative_continuous.comp affine_continuous).clm_comp continuous_const
  have pulledDerivative_derivative (position : ℂ) :
      HasFDerivAt (function ∘ affine) (pulledDerivative position) position :=
    (function_derivative (affine position)).comp position (affine_derivative position)
  have reynolds := nearCircleInterior_hasDerivAt_integral shape velocity shape_continuous velocity_continuous
    small time radius radius_positive equation (function ∘ affine) pulledDerivative
    (function_continuous.comp affine_continuous) pulledDerivative_continuous pulledDerivative_derivative
  have multiplied := reynolds.const_mul (scale ^ 2)
  have integral_identity :
      (fun parameter => ∫ position in affinePatchDomain center scale (shape parameter) (small parameter), function position) =
      (fun parameter => scale ^ 2 * ∫ position in nearCircleInterior (shape parameter) (small parameter), function (affine position)) := by
    funext parameter
    exact integral_affinePatchDomain center positive (shape parameter) (small parameter) function
  rw [integral_identity]
  convert multiplied using 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro label _
  dsimp only [Function.comp_apply, affine]
  rw [contourAreaPair_real_scaling]
  ring

end

end EulerNonuniqueness.Paper
