import EulerNonuniqueness.Section3.ContourAntilinearMoment

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance polynomialLineHolderSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance polynomialLineC1Space : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

theorem contour_affine_line_hasDerivAt (base direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => base + scalar • direction) direction 0 := by
  simpa only [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const direction).const_add base

theorem contour_linear_affine_line_hasDerivAt {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (operator : PeriodicC1HolderHalf →L[ℝ] Target) (base direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => operator (base + scalar • direction)) (operator direction) 0 := by
  have linearJet : HasFDerivAt operator operator (base + (0 : ℝ) • direction) :=
    ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := PeriodicC1HolderHalf) (F := Target) operator
  exact HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := PeriodicC1HolderHalf) (E := Target) 0
    linearJet (contour_affine_line_hasDerivAt base direction)

theorem contourPolynomialMoment_one_line_hasDerivAt (base direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 1 (base + scalar • direction))
      ((-Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        direction.val.1 label * star (base.val.1 label) * base.val.2.val.1 label +
        base.val.1 label * star (direction.val.1 label) * base.val.2.val.1 label +
        base.val.1 label * star (base.val.1 label) * direction.val.2.val.1 label) 0 := by
  have valueJet := contour_linear_affine_line_hasDerivAt contourValueFunctionCLM base direction
  have conjugateJet := contour_linear_affine_line_hasDerivAt (contourValueFunctionCLM.comp c1ConjugateCLM) base direction
  have tangentJet := contour_linear_affine_line_hasDerivAt contourTangentFunctionCLM base direction
  have productJet := (valueJet.mul conjugateJet).mul tangentJet
  have integralJet := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ →ᵇ ℂ) (E := ℂ) 0
    (boundedIntervalIntegral (-Real.pi) Real.pi).hasFDerivAt productJet
  have actual := integralJet.const_mul (-Complex.I / 2)
  convert actual using 1
  · funext scalar
    simp only [contourPolynomialMoment, pow_one, Function.comp_apply, ContinuousLinearMap.comp_apply]
  · congr 1
    apply intervalIntegral.integral_congr
    intro label _inside
    change _ = ((direction.val.1 label * star ((base + (0 : ℝ) • direction).val.1 label) +
      (base + (0 : ℝ) • direction).val.1 label * star (direction.val.1 label)) *
      (base + (0 : ℝ) • direction).val.2.val.1 label +
      ((base + (0 : ℝ) • direction).val.1 label * star ((base + (0 : ℝ) • direction).val.1 label)) * direction.val.2.val.1 label)
    simp only [zero_smul, add_zero]
    ring

theorem contourPolynomialMoment_zero_line_hasDerivAt (base direction : PeriodicC1HolderHalf) :
    HasDerivAt (fun scalar : ℝ => contourPolynomialMoment 0 (base + scalar • direction))
      ((-Complex.I / 2) * ∫ label in (-Real.pi)..Real.pi,
        star (direction.val.1 label) * base.val.2.val.1 label + star (base.val.1 label) * direction.val.2.val.1 label) 0 := by
  have conjugateJet := contour_linear_affine_line_hasDerivAt (contourValueFunctionCLM.comp c1ConjugateCLM) base direction
  have tangentJet := contour_linear_affine_line_hasDerivAt contourTangentFunctionCLM base direction
  have productJet := conjugateJet.mul tangentJet
  have integralJet := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := ℝ →ᵇ ℂ) (E := ℂ) 0
    (boundedIntervalIntegral (-Real.pi) Real.pi).hasFDerivAt productJet
  have actual := integralJet.const_mul (-Complex.I / 2)
  convert actual using 1
  · funext scalar
    simp only [contourPolynomialMoment, pow_zero, one_mul, Function.comp_apply, ContinuousLinearMap.comp_apply]
  · congr 1
    apply intervalIntegral.integral_congr
    intro label _inside
    change _ = star (direction.val.1 label) * (base + (0 : ℝ) • direction).val.2.val.1 label +
      star ((base + (0 : ℝ) • direction).val.1 label) * direction.val.2.val.1 label
    simp only [zero_smul, add_zero]

end EulerNonuniqueness.Paper
