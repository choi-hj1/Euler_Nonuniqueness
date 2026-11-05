import EulerNonuniqueness.Section3.ContourScalarGreen
import EulerNonuniqueness.Section8.RegularizedKernelDivergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open Set MeasureTheory
open scoped InnerProductSpace

namespace EulerNonuniqueness.Paper

noncomputable section

def regularizedContourLog (scale : ℝ) (point position : ℂ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (‖position - point‖ ^ 2 + scale ^ 2)

def regularizedContourLogDerivative (scale : ℝ) (point position : ℂ) : ℂ →L[ℝ] ℝ :=
  (‖position - point‖ ^ 2 + scale ^ 2)⁻¹ • innerSL ℝ (position - point)

theorem regularizedContourLog_hasFDerivAt {scale : ℝ} (positive : 0 < scale)
    (point position : ℂ) :
    HasFDerivAt (regularizedContourLog scale point)
      (regularizedContourLogDerivative scale point position) position := by
  have affine := (hasFDerivAt_id (𝕜 := ℝ) position).sub_const point
  have squared := affine.norm_sq
  have log_derivative := ((squared.add_const (scale ^ 2)).log
    (by positivity : ‖position - point‖ ^ 2 + scale ^ 2 ≠ 0)).const_mul (1 / 2 : ℝ)
  convert log_derivative using 1
  ext direction
  simp only [regularizedContourLogDerivative, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, innerSL_apply,
    smul_eq_mul, _root_.id]
  ring

theorem regularizedContourLog_continuous {scale : ℝ} (positive : 0 < scale) (point : ℂ) :
    Continuous (regularizedContourLog scale point) :=
  continuous_iff_continuousAt.mpr fun position =>
    (regularizedContourLog_hasFDerivAt positive point position).continuousAt

theorem regularizedContourLogDerivative_continuous {scale : ℝ} (positive : 0 < scale) (point : ℂ) :
    Continuous (regularizedContourLogDerivative scale point) := by
  unfold regularizedContourLogDerivative
  apply Continuous.smul
  · exact ((continuous_id.sub continuous_const).norm.pow 2 |>.add continuous_const).inv₀
      (fun position => by positivity)
  · fun_prop

theorem regularizedContourLog_complex_gradient {scale : ℝ} (positive : 0 < scale)
    (point position : ℂ) :
    ((regularizedContourLogDerivative scale point position 1 : ℝ) : ℂ) +
      Complex.I * (regularizedContourLogDerivative scale point position Complex.I : ℝ) =
      (‖position - point‖ ^ 2 + scale ^ 2)⁻¹ • (position - point) := by
  simp only [regularizedContourLogDerivative, ContinuousLinearMap.smul_apply, innerSL_apply,
    smul_eq_mul, real_inner_complex_one, real_inner_complex_I]
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

theorem regularizedBiotSavartKernel_eq_log_gradient {scale : ℝ} (positive : 0 < scale)
    (point position : ℂ) :
    regularizedBiotSavartKernel scale (point - position) =
      (-Complex.I / (2 * Real.pi : ℝ)) *
        ((‖position - point‖ ^ 2 + scale ^ 2)⁻¹ • (position - point)) := by
  have norm_identity : ‖point - position‖ = ‖position - point‖ := norm_sub_rev _ _
  rw [regularizedBiotSavartKernel, norm_identity]
  simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_mul]
  ring

theorem integral_nearCircleInterior_regularizedBiotSavart
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    {scale : ℝ} (positive : 0 < scale) (point : ℂ) :
    (∫ position in nearCircleInterior data small, regularizedBiotSavartKernel scale (point - position)) =
      -(2 * Real.pi)⁻¹ • (∫ label in (-Real.pi)..Real.pi,
        regularizedContourLog scale point (data.val.1 label) • data.val.2.val.1 label) := by
  have green := integral_nearCircleInterior_complex_gradient data small
    (regularizedContourLog scale point) (regularizedContourLogDerivative scale point)
    (regularizedContourLog_continuous positive point)
    (regularizedContourLogDerivative_continuous positive point)
    (regularizedContourLog_hasFDerivAt positive point)
  simp_rw [regularizedContourLog_complex_gradient positive] at green
  simp_rw [regularizedBiotSavartKernel_eq_log_gradient positive]
  rw [integral_const_mul, green]
  let boundary : ℂ := ∫ label in (-Real.pi)..Real.pi,
    regularizedContourLog scale point (data.val.1 label) • data.val.2.val.1 label
  change (-Complex.I / (2 * Real.pi : ℝ)) * (-Complex.I * boundary) = -(2 * Real.pi)⁻¹ • boundary
  simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_inv]
  push_cast
  calc
    _ = (Complex.I * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)⁻¹ * boundary := by push_cast; ring
    _ = _ := by rw [Complex.I_mul_I]; push_cast; ring

end

end EulerNonuniqueness.Paper
