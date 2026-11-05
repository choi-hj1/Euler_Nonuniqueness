import EulerNonuniqueness.Section3.ContourWeightedGreen
import EulerNonuniqueness.Section8.RegularizedVelocityDifference
import EulerNonuniqueness.Section8.RegularizedKernelLipschitz
import EulerNonuniqueness.Section8.RegularizedKernelDivergence
import EulerNonuniqueness.Section8.LagrangianDivergence

open Set MeasureTheory
open scoped NNReal ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

def regularizedContourVelocityDerivative (scale : ℝ) (source : Vorticity) (position : ℂ) : ℂ →L[ℝ] ℂ :=
  lagrangianVelocityDerivative source (regularizedBiotSavartKernel scale) 0 position

theorem regularizedContourKernel_operator_bound {scale : ℝ} (positive : 0 < scale) (position : ℂ) :
    ‖fderiv ℝ (regularizedBiotSavartKernel scale) position‖ ≤ 3 / (2 * Real.pi * scale ^ 2) :=
  (fderiv ℝ (regularizedBiotSavartKernel scale) position).opNorm_le_bound (by positivity)
    (norm_fderiv_regularizedBiotSavartKernel_le positive position)

theorem regularizedBiotSavart_hasFDerivAt {scale : ℝ} (positive : 0 < scale)
    {source : Vorticity} (integrable : Integrable source) (position : ℂ) :
    HasFDerivAt (regularizedBiotSavart scale source)
      (regularizedContourVelocityDerivative scale source position) position := by
  have kernel_smooth : ContDiff ℝ 1 (regularizedBiotSavartKernel scale) :=
    (contDiff_regularizedBiotSavartKernel positive).of_le (by simp)
  have derivative := hasFDerivAt_lagrangianVelocity integrable kernel_smooth
    (bound := ⟨1 / (2 * Real.pi * scale), by positivity⟩)
    (derivativeBound := ⟨3 / (2 * Real.pi * scale ^ 2), by positivity⟩)
    (norm_regularizedBiotSavartKernel_le positive) (regularizedContourKernel_operator_bound positive) 0 position
  have identity : lagrangianVelocity source (regularizedBiotSavartKernel scale) 0 =
      regularizedBiotSavart scale source := by
    funext point
    simp [lagrangianVelocity, regularizedBiotSavart]
  rw [identity] at derivative
  exact derivative

theorem regularizedContourVelocityDerivative_continuous {scale : ℝ} (positive : 0 < scale)
    {source : Vorticity} (integrable : Integrable source) :
    Continuous (regularizedContourVelocityDerivative scale source) := by
  have kernel_smooth : ContDiff ℝ 1 (regularizedBiotSavartKernel scale) :=
    (contDiff_regularizedBiotSavartKernel positive).of_le (by simp)
  have joint := continuous_lagrangianVelocityDerivative integrable kernel_smooth
    (derivativeBound := ⟨3 / (2 * Real.pi * scale ^ 2), by positivity⟩)
    (regularizedContourKernel_operator_bound positive)
  exact joint.comp (continuous_const.prodMk continuous_id)

theorem regularizedContourVelocityDerivative_trace_zero {scale : ℝ} (positive : 0 < scale)
    {source : Vorticity} (integrable : Integrable source) (position : ℂ) :
    contourPlaneTrace (regularizedContourVelocityDerivative scale source position) = 0 := by
  have kernel_smooth : ContDiff ℝ 1 (regularizedBiotSavartKernel scale) :=
    (contDiff_regularizedBiotSavartKernel positive).of_le (by simp)
  exact lagrangianVelocityDerivative_trace_zero integrable kernel_smooth
    (derivativeBound := ⟨3 / (2 * Real.pi * scale ^ 2), by positivity⟩)
    (regularizedContourKernel_operator_bound positive) (divergence_regularizedBiotSavartKernel positive) 0 position

theorem integral_nearCircleInterior_regularized_advection
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → ℝ) (derivative : ℂ → ℂ →L[ℝ] ℝ)
    (function_continuous : Continuous function) (derivative_continuous : Continuous derivative)
    (function_derivative : ∀ position, HasFDerivAt function (derivative position) position)
    {scale : ℝ} (positive : 0 < scale) {source : Vorticity} (integrable : Integrable source) :
    (∫ position in nearCircleInterior data small, derivative position (regularizedBiotSavart scale source position)) =
      ∫ label in (-Real.pi)..Real.pi, function (data.val.1 label) *
        contourAreaPair (regularizedBiotSavart scale source (data.val.1 label)) (data.val.2.val.1 label) := by
  have field_continuous : Continuous (regularizedBiotSavart scale source) :=
    continuous_iff_continuousAt.mpr fun position =>
      (regularizedBiotSavart_hasFDerivAt positive integrable position).continuousAt
  exact integral_nearCircleInterior_directional_field data small function derivative
    function_continuous derivative_continuous function_derivative
    (regularizedBiotSavart scale source) (regularizedContourVelocityDerivative scale source)
    field_continuous (regularizedContourVelocityDerivative_continuous positive integrable)
    (regularizedBiotSavart_hasFDerivAt positive integrable)
    (regularizedContourVelocityDerivative_trace_zero positive integrable)

end

end EulerNonuniqueness.Paper
