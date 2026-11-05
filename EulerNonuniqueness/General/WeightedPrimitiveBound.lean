import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem norm_integral_weight_mul_le_primitive
    {source weight weightDerivative : ℝ → ℂ} {terminal weightBound derivativeBound primitiveBound : ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (sourceContinuous : ContinuousOn source (Icc 0 terminal))
    (weightContinuous : ContinuousOn weight (Icc 0 terminal))
    (derivativeContinuous : ContinuousOn weightDerivative (Icc 0 terminal))
    (weightEquation : ∀ time ∈ Ioo 0 terminal, HasDerivAt weight (weightDerivative time) time)
    (weightControl : ∀ time ∈ Icc 0 terminal, ‖weight time‖ ≤ weightBound)
    (derivativeControl : ∀ time ∈ Icc 0 terminal, ‖weightDerivative time‖ ≤ derivativeBound)
    (primitiveControl : ∀ time ∈ Icc 0 terminal, ‖∫ current in (0 : ℝ)..time, source current‖ ≤ primitiveBound) :
    ‖∫ time in (0 : ℝ)..terminal, weight time * source time‖ ≤
      (weightBound + terminal * derivativeBound) * primitiveBound := by
  let primitive : ℝ → ℂ := fun time => ∫ current in (0 : ℝ)..time, source current
  have initialInside : (0 : ℝ) ∈ Icc 0 terminal := ⟨le_rfl, terminalNonnegative⟩
  have derivativeBoundNonnegative := (norm_nonneg (weightDerivative 0)).trans (derivativeControl 0 initialInside)
  have primitiveBoundNonnegative := (norm_nonneg (primitive 0)).trans (primitiveControl 0 initialInside)
  have sourceContinuousUnordered : ContinuousOn source (uIcc 0 terminal) := by
    simpa only [uIcc_of_le terminalNonnegative] using sourceContinuous
  have weightContinuousUnordered : ContinuousOn weight (uIcc 0 terminal) := by
    simpa only [uIcc_of_le terminalNonnegative] using weightContinuous
  have derivativeContinuousUnordered : ContinuousOn weightDerivative (uIcc 0 terminal) := by
    simpa only [uIcc_of_le terminalNonnegative] using derivativeContinuous
  have sourceIntegrable : IntervalIntegrable source volume 0 terminal := sourceContinuousUnordered.intervalIntegrable
  have primitiveContinuous : ContinuousOn primitive (uIcc 0 terminal) :=
    intervalIntegral.continuousOn_primitive_interval' sourceIntegrable left_mem_uIcc
  have primitiveEquation (time : ℝ) (inside : time ∈ Ioo 0 terminal) : HasDerivAt primitive (source time) time := by
    have sourceInterior : ContinuousOn source (Ioo 0 terminal) := sourceContinuous.mono Ioo_subset_Icc_self
    have measurable := ContinuousOn.stronglyMeasurableAtFilter (μ := volume) isOpen_Ioo sourceInterior time inside
    have atTime := sourceInterior.continuousAt (isOpen_Ioo.mem_nhds inside)
    have integrable := sourceIntegrable.mono_set (show uIcc (0 : ℝ) time ⊆ uIcc 0 terminal by
      rw [uIcc_of_le inside.1.le, uIcc_of_le terminalNonnegative]
      exact Icc_subset_Icc le_rfl inside.2.le)
    exact intervalIntegral.integral_hasDerivAt_right integrable measurable atTime
  have identity := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt weightContinuousUnordered primitiveContinuous
    (by simpa only [min_eq_left terminalNonnegative, max_eq_right terminalNonnegative] using weightEquation)
    (by simpa only [min_eq_left terminalNonnegative, max_eq_right terminalNonnegative] using primitiveEquation)
    derivativeContinuousUnordered.intervalIntegrable sourceIntegrable
  have primitiveZero : primitive 0 = 0 := intervalIntegral.integral_same
  rw [primitiveZero, mul_zero, sub_zero] at identity
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun time => weightDerivative time * primitive time)
    (show ∀ time ∈ uIoc 0 terminal, ‖weightDerivative time * primitive time‖ ≤ derivativeBound * primitiveBound from by
      intro time inside
      rw [uIoc_of_le terminalNonnegative] at inside
      rw [norm_mul]
      exact mul_le_mul (derivativeControl time ⟨inside.1.le, inside.2⟩) (primitiveControl time ⟨inside.1.le, inside.2⟩)
        (norm_nonneg _) derivativeBoundNonnegative)
  rw [sub_zero, abs_of_nonneg terminalNonnegative] at integralBound
  rw [identity]
  have endpointBound : ‖weight terminal * primitive terminal‖ ≤ weightBound * primitiveBound := by
    rw [norm_mul]
    exact mul_le_mul (weightControl terminal ⟨terminalNonnegative, le_rfl⟩) (primitiveControl terminal ⟨terminalNonnegative, le_rfl⟩)
      (norm_nonneg _) ((norm_nonneg (weight 0)).trans (weightControl 0 initialInside))
  exact (norm_sub_le _ _).trans ((add_le_add endpointBound integralBound).trans_eq (by ring))

end EulerNonuniqueness
