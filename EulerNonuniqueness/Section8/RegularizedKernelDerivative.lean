import EulerNonuniqueness.Section8.RegularizedKernel

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff InnerProductSpace

namespace EulerNonuniqueness

theorem fderiv_regularizedBiotSavartKernel {scale : ℝ} (positive : 0 < scale) (position direction : Plane) :
    fderiv ℝ (regularizedBiotSavartKernel scale) position direction =
      (2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2))⁻¹ • (Complex.I * direction) +
        (-((2 * Real.pi * (‖position‖ ^ 2 + scale ^ 2)) ^ 2)⁻¹ *
          (2 * Real.pi * (2 * ⟪position, direction⟫_ℝ))) • (Complex.I * position) := by
  let denominator := fun other : Plane => 2 * Real.pi * (‖other‖ ^ 2 + scale ^ 2)
  have denominatorPositive : 0 < denominator position := by dsimp [denominator]; positivity
  have identityDerivative : HasFDerivAt (fun other : Plane => other) (ContinuousLinearMap.id ℝ Plane) position := hasFDerivAt_id position
  have radial : HasFDerivAt (fun other : Plane => ‖other‖ ^ 2) (2 • innerSL ℝ position) position := by
    simpa only [ContinuousLinearMap.comp_id] using identityDerivative.norm_sq
  have denominatorDerivative : HasFDerivAt denominator ((2 * Real.pi) • 2 • innerSL ℝ position) position :=
    (radial.add_const (scale ^ 2)).const_mul (2 * Real.pi)
  have reciprocal : HasFDerivAt (fun other => (denominator other)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-(denominator position ^ 2)⁻¹)).comp
        ((2 * Real.pi) • 2 • innerSL ℝ position)) position :=
    (hasFDerivAt_inv denominatorPositive.ne').comp position denominatorDerivative
  have constantDerivative : HasFDerivAt (fun _ : Plane => Complex.I) (0 : Plane →L[ℝ] Plane) position := hasFDerivAt_const Complex.I position
  have numerator : HasFDerivAt (fun other : Plane => Complex.I * other) (Complex.I • ContinuousLinearMap.id ℝ Plane) position := by
    simpa only [smul_zero, add_zero] using constantDerivative.mul identityDerivative
  have derivative := reciprocal.smul numerator
  have equality : (fun other : Plane => (2 * Real.pi * (‖other‖ ^ 2 + scale ^ 2))⁻¹ • (Complex.I * other)) =
      regularizedBiotSavartKernel scale := by
    funext other
    simp only [regularizedBiotSavartKernel, Complex.real_smul, Complex.ofReal_inv, div_eq_mul_inv]
    ring
  simp only [Function.comp_apply, denominator, _root_.id] at derivative
  rw [equality] at derivative
  rw [derivative.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    zero_mul, add_zero, mul_zero, zero_add, innerSL_apply, smul_eq_mul, ContinuousLinearMap.one_apply]
  congr 1
  apply congrArg (fun coefficient : ℝ => coefficient • (Complex.I * position))
  simp only [two_smul, smul_eq_mul]
  ring

end EulerNonuniqueness
