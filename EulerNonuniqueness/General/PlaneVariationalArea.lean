import Mathlib

noncomputable section

open Set
open scoped Topology

namespace Complex

def orientedArea (first second : ℂ) : ℝ := first.re * second.im - first.im * second.re

theorem orientedArea_linear_derivative (coefficient : ℂ →L[ℝ] ℂ) (first second : ℂ) :
    orientedArea (coefficient first) second + orientedArea first (coefficient second) =
      ((coefficient 1).re + (coefficient I).im) * orientedArea first second := by
  have decompose (position : ℂ) : position = position.re • (1 : ℂ) + position.im • I := by
    apply Complex.ext <;> simp [Complex.real_smul]
  have applyEquality (position : ℂ) : coefficient position =
      position.re • coefficient 1 + position.im • coefficient I := by
    conv_lhs => rw [decompose position]
    rw [map_add, map_smul, map_smul]
  rw [applyEquality first, applyEquality second]
  simp only [orientedArea, add_re, add_im, Complex.real_smul, mul_re, mul_im,
    ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add]
  ring

theorem hasDerivWithinAt_orientedArea {first second : ℝ → ℂ} {firstDerivative secondDerivative : ℂ}
    {region : Set ℝ} {time : ℝ}
    (firstDifferentiable : HasDerivWithinAt first firstDerivative region time)
    (secondDifferentiable : HasDerivWithinAt second secondDerivative region time) :
    HasDerivWithinAt (fun time => orientedArea (first time) (second time))
      (orientedArea firstDerivative (second time) + orientedArea (first time) secondDerivative) region time := by
  have firstReal := reCLM.hasFDerivAt.comp_hasDerivWithinAt time firstDifferentiable
  have firstImaginary := imCLM.hasFDerivAt.comp_hasDerivWithinAt time firstDifferentiable
  have secondReal := reCLM.hasFDerivAt.comp_hasDerivWithinAt time secondDifferentiable
  have secondImaginary := imCLM.hasFDerivAt.comp_hasDerivWithinAt time secondDifferentiable
  convert (firstReal.mul secondImaginary).sub (firstImaginary.mul secondReal) using 1
  dsimp [orientedArea]
  ring

theorem orientedArea_constant_of_trace_zero
    {coefficient : ℝ → ℂ →L[ℝ] ℂ} {first second : ℝ → ℂ} {start finish : ℝ}
    (firstContinuous : ContinuousOn first (Icc start finish))
    (secondContinuous : ContinuousOn second (Icc start finish))
    (firstEquation : ∀ time ∈ Ico start finish,
      HasDerivWithinAt first (coefficient time (first time)) (Ici time) time)
    (secondEquation : ∀ time ∈ Ico start finish,
      HasDerivWithinAt second (coefficient time (second time)) (Ici time) time)
    (traceZero : ∀ time ∈ Ico start finish, (coefficient time 1).re + (coefficient time I).im = 0) :
    ∀ time ∈ Icc start finish, orientedArea (first time) (second time) = orientedArea (first start) (second start) := by
  apply constant_of_has_deriv_right_zero
  · exact ((reCLM.continuous.comp_continuousOn firstContinuous).mul
      (imCLM.continuous.comp_continuousOn secondContinuous)).sub
        ((imCLM.continuous.comp_continuousOn firstContinuous).mul
          (reCLM.continuous.comp_continuousOn secondContinuous))
  · intro time inside
    have derivative := hasDerivWithinAt_orientedArea (firstEquation time inside) (secondEquation time inside)
    rwa [orientedArea_linear_derivative, traceZero time inside, zero_mul] at derivative

end Complex
