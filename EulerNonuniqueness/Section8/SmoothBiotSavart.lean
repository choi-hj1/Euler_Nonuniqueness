import EulerNonuniqueness.Section8.SpatialRegularity
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section

open MeasureTheory Set
open scoped ENNReal Topology ContDiff Convolution

namespace EulerNonuniqueness

theorem fderiv_biotSavart_apply {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (position direction : Plane) :
    fderiv ℝ (biotSavart vorticity) position direction =
      biotSavart (fun source => fderiv ℝ vorticity source direction) position := by
  have derivative := compact.hasFDerivAt_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (smooth.of_le (by simp))
    locallyIntegrable_biotSavartKernel position
  change fderiv ℝ (vorticity ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] biotSavartKernel)
    position direction = _
  rw [derivative.fderiv]
  have integrable := (compact.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Plane)
    (smooth.continuous_fderiv (by simp)) locallyIntegrable_biotSavartKernel position
  simp_rw [convolution_def]
  rw [ContinuousLinearMap.integral_apply integrable]
  rfl

theorem integral_directionalDerivative_eq_zero {function : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ function) (compact : HasCompactSupport function) (direction : Plane) :
    (∫ position, fderiv ℝ function position direction) = 0 := by
  have derivativeContinuous : Continuous (fun position => fderiv ℝ function position direction) :=
    (smooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have derivativeIntegrable := derivativeContinuous.integrable_of_hasCompactSupport
    (compact.fderiv_apply ℝ direction) (μ := volume)
  have integrable := smooth.continuous.integrable_of_hasCompactSupport compact (μ := volume)
  have identity := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Plane => (1 : ℝ)) (g := function) (v := direction)
    (by simp)
    (by simpa using derivativeIntegrable) (by simpa using integrable)
    (differentiable_const 1) (smooth.differentiable (by simp))
  simpa using identity

theorem memLp_biotSavart_two_of_continuous_compactSupport_integral_zero {vorticity : Vorticity}
    (continuous : Continuous vorticity) (compact : HasCompactSupport vorticity)
    (zeroMean : (∫ position, vorticity position) = 0) :
    MemLp (biotSavart vorticity) 2 volume := by
  obtain ⟨radius, radiusPositive, supportBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  obtain ⟨bound, boundPositive, boundAt⟩ :=
    (compact.isCompact.image continuous).isBounded.exists_pos_norm_le
  apply memLp_biotSavart_two_of_bounded_support_integral_zero
    (continuous.integrable_of_hasCompactSupport compact) zeroMean radiusPositive.le
  · intro source nonzero
    simpa using supportBound source (subset_tsupport _ nonzero)
  · intro source
    by_cases zero : vorticity source = 0
    · simpa [zero] using boundPositive.le
    · simpa [Real.norm_eq_abs] using
        boundAt _ ⟨source, subset_tsupport _ (Function.mem_support.mpr zero), rfl⟩

theorem memLp_fderiv_biotSavart_apply {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (direction : Plane) :
    MemLp (fun position => fderiv ℝ (biotSavart vorticity) position direction) 2 volume := by
  have equality : (fun position => fderiv ℝ (biotSavart vorticity) position direction) =
      biotSavart (fun source => fderiv ℝ vorticity source direction) :=
    funext fun position => fderiv_biotSavart_apply smooth compact position direction
  rw [equality]
  exact memLp_biotSavart_two_of_continuous_compactSupport_integral_zero
    ((smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
    (compact.fderiv_apply ℝ direction) (integral_directionalDerivative_eq_zero smooth compact direction)

theorem memLp_second_fderiv_biotSavart_apply {vorticity : Vorticity}
    (smooth : ContDiff ℝ ∞ vorticity) (compact : HasCompactSupport vorticity)
    (firstDirection secondDirection : Plane) :
    MemLp (fun position =>
      fderiv ℝ (fun point => fderiv ℝ (biotSavart vorticity) point firstDirection)
        position secondDirection) 2 volume := by
  have equality : (fun position => fderiv ℝ (biotSavart vorticity) position firstDirection) =
      biotSavart (fun source => fderiv ℝ vorticity source firstDirection) :=
    funext fun position => fderiv_biotSavart_apply smooth compact position firstDirection
  rw [equality]
  exact memLp_fderiv_biotSavart_apply
    ((smooth.fderiv_right (by simp)).clm_apply contDiff_const)
    (compact.fderiv_apply ℝ firstDirection) secondDirection

theorem fderiv_realLinearMap_comp_apply {function : Plane → Plane}
    (smooth : ContDiff ℝ ∞ function) (linear : Plane →L[ℝ] ℝ)
    (position direction : Plane) :
    fderiv ℝ (linear ∘ function) position direction =
      linear (fderiv ℝ function position direction) := by
  have derivative := linear.hasFDerivAt.comp position
    (smooth.differentiable (by simp) position).hasFDerivAt
  exact congrArg (fun derivative : Plane →L[ℝ] ℝ => derivative direction) derivative.fderiv

end EulerNonuniqueness
