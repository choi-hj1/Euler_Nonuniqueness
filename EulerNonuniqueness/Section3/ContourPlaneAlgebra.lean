import EulerNonuniqueness.Section3.NearCircleInterior
import Mathlib.Analysis.Calculus.Deriv.Star

namespace EulerNonuniqueness.Paper

noncomputable section

def contourAreaPair (first second : ℂ) : ℝ := (star first * second).im

theorem hasDerivAt_contourAreaPair {first second : ℝ → ℂ} {first' second' : ℂ} {time : ℝ}
    (first_derivative : HasDerivAt first first' time)
    (second_derivative : HasDerivAt second second' time) :
    HasDerivAt (fun parameter => contourAreaPair (first parameter) (second parameter))
      (contourAreaPair first' (second time) + contourAreaPair (first time) second') time := by
  have derivative := Complex.imCLM.hasFDerivAt.comp_hasDerivAt time
    (first_derivative.star.mul second_derivative)
  simpa only [contourAreaPair, map_add] using derivative

theorem continuous_contourAreaPair : Continuous (fun pair : ℂ × ℂ => contourAreaPair pair.1 pair.2) :=
  Complex.continuous_im.comp (continuous_fst.star.mul continuous_snd)

theorem contourAreaPair_coordinates (first second : ℂ) :
    contourAreaPair first second = first.re * second.im - first.im * second.re := by
  simp only [contourAreaPair, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem contourAreaPair_swap (first second : ℂ) : contourAreaPair first second = -contourAreaPair second first := by
  rw [contourAreaPair_coordinates, contourAreaPair_coordinates]
  ring

theorem realLinear_complex_expansion (linear : ℂ →L[ℝ] ℂ) (position : ℂ) :
    linear position = position.re • linear 1 + position.im • linear Complex.I := by
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  apply Complex.ext <;> simp [Complex.real_smul]

theorem realLinear_scalar_expansion (linear : ℂ →L[ℝ] ℝ) (position : ℂ) :
    linear position = position.re * linear 1 + position.im * linear Complex.I := by
  change linear position = position.re • linear 1 + position.im • linear Complex.I
  rw [← map_smul, ← map_smul, ← map_add]
  congr 1
  apply Complex.ext <;> simp [Complex.real_smul]

def contourPlaneTrace (linear : ℂ →L[ℝ] ℂ) : ℝ := (linear 1).re + (linear Complex.I).im

theorem contourAreaPair_linear_trace (linear : ℂ →L[ℝ] ℂ) (first second : ℂ) :
    contourAreaPair (linear first) second + contourAreaPair first (linear second) =
      contourPlaneTrace linear * contourAreaPair first second := by
  rw [contourAreaPair_coordinates, contourAreaPair_coordinates, contourAreaPair_coordinates,
    realLinear_complex_expansion linear first, realLinear_complex_expansion linear second]
  simp only [contourPlaneTrace, Complex.add_re, Complex.add_im, Complex.real_smul,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, zero_add]
  ring

theorem contourAreaPair_scalar_identity (linear : ℂ →L[ℝ] ℝ) (position tangent velocity : ℂ) :
    linear velocity * contourAreaPair position tangent =
      linear position * contourAreaPair velocity tangent + linear tangent * contourAreaPair position velocity := by
  rw [realLinear_scalar_expansion linear velocity, realLinear_scalar_expansion linear position,
    realLinear_scalar_expansion linear tangent, contourAreaPair_coordinates, contourAreaPair_coordinates,
    contourAreaPair_coordinates]
  ring

end

end EulerNonuniqueness.Paper
