import EulerNonuniqueness.Section3.NormalizedExteriorKernelC1Relative
import EulerNonuniqueness.Section3.C1ContourEvaluation

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

theorem normalizedC1Reciprocal_zero (parameter : ℂ) :
    normalizedC1Reciprocal parameter 0 = c1Constant 1 := by
  unfold normalizedC1Reciprocal normalizedC1Denominator
  rw [map_zero, add_zero, extendedC1Inverse_one]

theorem normalizedExteriorKernelC1_zero (parameter : ℂ) (power : ℕ) :
    normalizedExteriorKernelC1 parameter power 0 = 0 := by
  rw [normalizedExteriorKernelC1, normalizedC1Reciprocal_zero, c1NaturalPower_constant_one,
    c1Conjugate_constant_one, sub_self]

theorem normalizedExteriorKernelC1_exists_derivative_zero :
    ∃ parameterRadius > (0 : ℝ), ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius →
      ∀ power : ℕ, ∀ direction : PeriodicC1HolderHalf, ∀ label : ℝ,
        (normalizedExteriorKernelC1Derivative parameter power 0 direction).val.1 label =
          (power + 1 : ℂ) * star parameter * star (direction.val.1 label) := by
  obtain ⟨parameterRadius, positive, constant, one, bound⟩ := normalizedC1Reciprocal_exists_uniform_bounds
  obtain ⟨kernelRadius, kernelPositive, kernelConstant, kernelOne, kernelBound⟩ :=
    normalizedExteriorKernelC1_exists_uniform_bounds
  refine ⟨min parameterRadius kernelRadius, lt_min positive kernelPositive, ?_⟩
  intro parameter small power direction label
  have parameterSmall := small.trans (min_le_left _ _)
  have kernelSmall := small.trans (min_le_right _ _)
  have actualKernel := (kernelBound parameter kernelSmall power 0 (by simp)).2.1
  have line : HasDerivAt (fun scalar : ℝ => scalar • direction) direction 0 := by
    simpa only [one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const direction
  have actualAtLine : HasFDerivAt (normalizedExteriorKernelC1 parameter power)
      (normalizedExteriorKernelC1Derivative parameter power 0) ((0 : ℝ) • direction) := by
    simpa only [zero_smul] using actualKernel
  have actual := hasDerivAt_contour_value (actualAtLine.comp_hasDerivAt 0 line) label
  have near : ∀ᶠ scalar : ℝ in 𝓝 0, ‖scalar • direction‖ ≤ 3 := by
    have continuous : ContinuousAt (fun scalar : ℝ => ‖scalar • direction‖) 0 := by fun_prop
    have convergence : Tendsto (fun scalar : ℝ => ‖scalar • direction‖) (𝓝 0) (𝓝 (0 : ℝ)) := by
      simpa only [zero_smul, norm_zero] using continuous.tendsto
    exact (convergence.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 3))).mono fun _ inside => inside.le
  have equalNear : (fun scalar : ℝ => (normalizedExteriorKernelC1 parameter power (scalar • direction)).val.1 label) =ᶠ[𝓝 0]
      (fun scalar : ℝ => (star (1 - parameter * ((scalar : ℂ) * direction.val.1 label)))⁻¹ ^ (power + 1) - 1) := by
    filter_upwards [near] with scalar inside
    have identity := normalizedExteriorKernelC1_value parameter power (scalar • direction)
      (((bound parameter parameterSmall).1 (scalar • direction) inside).1) label
    simpa only [normalizedExteriorInversePowerKernel, Complex.real_smul] using identity
  have affine : HasDerivAt (fun scalar : ℝ => (1 : ℂ) - parameter * ((scalar : ℂ) * direction.val.1 label))
      (-(parameter * direction.val.1 label)) 0 := by
    simpa using (((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (direction.val.1 label)).const_mul parameter).const_sub 1
  have inverseAt : HasFDerivAt (fun value : ℂ => value⁻¹)
      (-ContinuousLinearMap.mulLeftRight ℝ ℂ (1 : ℂ) (1 : ℂ))
      (star (1 - parameter * (((0 : ℝ) : ℂ) * direction.val.1 label))) := by
    simpa using (hasFDerivAt_inv' (𝕜 := ℝ) (show (1 : ℂ) ≠ 0 by norm_num))
  have inverse : HasDerivAt
      (fun scalar : ℝ => (star (1 - parameter * ((scalar : ℂ) * direction.val.1 label)))⁻¹)
      (star (parameter * direction.val.1 label)) 0 := by
    simpa using inverseAt.comp_hasDerivAt 0 affine.star
  have powerAt := (hasDerivAt_pow (power + 1) (1 : ℂ)).hasFDerivAt.restrictScalars ℝ
  have powerAtImage : HasFDerivAt (fun value : ℂ => value ^ (power + 1))
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
        ((power + 1 : ℂ) * (1 : ℂ) ^ power)).restrictScalars ℝ)
      ((star (1 - parameter * (((0 : ℝ) : ℂ) * direction.val.1 label)))⁻¹) := by
    simpa using powerAt
  have explicit := (powerAtImage.comp_hasDerivAt 0 inverse).sub_const 1
  have unique := (actual.congr_of_eventuallyEq equalNear.symm).unique explicit
  simpa [ContinuousLinearMap.coe_restrictScalars', star_mul, mul_comm, mul_left_comm, mul_assoc] using unique

end EulerNonuniqueness.Paper
