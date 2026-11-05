import EulerNonuniqueness.General.InteriorDerivativeError
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem norm_weighted_integral_le_of_interior_primitive_bound
    {source : ℝ → ℂ} {weight weightDerivative : ℝ → ℝ}
    {terminal primitiveBound derivativeBound weightBound : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (primitiveNonnegative : 0 ≤ primitiveBound)
    (derivativeNonnegative : 0 ≤ derivativeBound)
    (sourceContinuous : ContinuousOn source (Icc 0 terminal))
    (weightContinuous : ContinuousOn weight (Icc 0 terminal))
    (weightEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt weight (weightDerivative time) time)
    (weightControl : |weight terminal| ≤ weightBound)
    (derivativeControl : ∀ time ∈ Ioo 0 terminal, |weightDerivative time| ≤ derivativeBound)
    (primitiveControl : ∀ time ∈ Icc 0 terminal,
      ‖∫ current in (0 : ℝ)..time, source current‖ ≤ primitiveBound) :
    ‖∫ time in (0 : ℝ)..terminal, (weight time : ℂ) * source time‖ ≤
      (weightBound + derivativeBound * terminal) * primitiveBound := by
  let extension := fun time => source (projIcc 0 terminal terminalNonnegative time)
  have extensionContinuous : Continuous extension :=
    (continuousOn_iff_continuous_restrict.mp sourceContinuous).comp continuous_projIcc
  have agreement (time : ℝ) (inside : time ∈ Icc 0 terminal) : extension time = source time := by
    simp only [extension, projIcc_of_mem terminalNonnegative inside]
  let primitive := fun time => ∫ current in (0 : ℝ)..time, extension current
  have primitiveEquation (time : ℝ) : HasDerivAt primitive (extension time) time :=
    intervalIntegral.integral_hasDerivAt_right (extensionContinuous.intervalIntegrable 0 time)
      extensionContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter extensionContinuous.continuousAt
  have primitiveContinuous : Continuous primitive :=
    continuous_iff_continuousAt.mpr fun time => (primitiveEquation time).continuousAt
  have primitiveIdentity (time : ℝ) (inside : time ∈ Icc 0 terminal) :
      primitive time = ∫ current in (0 : ℝ)..time, source current := by
    apply intervalIntegral.integral_congr
    intro current member
    rw [uIcc_of_le inside.1] at member
    exact agreement current ⟨member.1, member.2.trans inside.2⟩
  have primitiveEstimate (time : ℝ) (inside : time ∈ Icc 0 terminal) : ‖primitive time‖ ≤ primitiveBound := by
    rw [primitiveIdentity time inside]
    exact primitiveControl time inside
  have actual := norm_sub_integral_le_of_interior_derivative_error
    (function := fun time => (weight time : ℂ) * primitive time)
    (derivative := fun time => (weightDerivative time : ℂ) * primitive time + (weight time : ℂ) * source time)
    (source := fun time => (weight time : ℂ) * source time)
    terminalNonnegative (mul_nonneg derivativeNonnegative primitiveNonnegative)
    ((Complex.continuous_ofReal.comp_continuousOn weightContinuous).mul primitiveContinuous.continuousOn)
    (fun time member => by
      simpa only [agreement time ⟨member.1.le, member.2.le⟩] using
        (weightEquation time member).ofReal_comp.mul (primitiveEquation time))
    ((Complex.continuous_ofReal.comp_continuousOn weightContinuous).mul sourceContinuous)
    (fun time member => by
      rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (derivativeControl time member)
        (primitiveEstimate time ⟨member.1.le, member.2.le⟩) (norm_nonneg _) derivativeNonnegative)
  have primitiveZero : primitive 0 = 0 := intervalIntegral.integral_same
  change ‖(weight terminal : ℂ) * primitive terminal - (weight 0 : ℂ) * primitive 0 -
    ∫ time in (0 : ℝ)..terminal, (weight time : ℂ) * source time‖ ≤
      derivativeBound * primitiveBound * terminal at actual
  rw [primitiveZero, mul_zero, sub_zero] at actual
  calc
    _ = ‖(weight terminal : ℂ) * primitive terminal -
        ((weight terminal : ℂ) * primitive terminal -
          ∫ time in (0 : ℝ)..terminal, (weight time : ℂ) * source time)‖ := by congr 1; abel
    _ ≤ ‖(weight terminal : ℂ) * primitive terminal‖ +
        ‖(weight terminal : ℂ) * primitive terminal -
          ∫ time in (0 : ℝ)..terminal, (weight time : ℂ) * source time‖ := norm_sub_le _ _
    _ ≤ weightBound * primitiveBound + derivativeBound * primitiveBound * terminal := by
      apply add_le_add _ actual
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul weightControl (primitiveEstimate terminal ⟨terminalNonnegative, le_rfl⟩)
        (norm_nonneg _) ((abs_nonneg (weight terminal)).trans weightControl)
    _ = _ := by ring

end EulerNonuniqueness
