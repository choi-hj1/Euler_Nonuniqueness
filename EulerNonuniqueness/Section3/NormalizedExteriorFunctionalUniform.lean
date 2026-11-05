import EulerNonuniqueness.Section3.NormalizedExteriorFunctional
import EulerNonuniqueness.Section3.NormalizedExteriorKernelUniform

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace
  EulerNonuniqueness.General.trilinearKernelBilinearGroup
  EulerNonuniqueness.General.trilinearKernelBilinearSpace
  EulerNonuniqueness.General.trilinearKernelThirdGroup
  EulerNonuniqueness.General.trilinearKernelThirdSpace

local instance functionalUniformBilinearGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance functionalUniformBilinearSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace
local instance functionalUniformThirdGroup : NormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance functionalUniformThirdSeminormedGroup : SeminormedAddCommGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  functionalUniformThirdGroup.toSeminormedAddCommGroup
local instance functionalUniformThirdSeminormedAddGroup : SeminormedAddGroup
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  functionalUniformThirdSeminormedGroup.toSeminormedAddGroup
local instance functionalUniformThirdSpace : NormedSpace ℝ
    (PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf →L[ℝ] ℂ) :=
  ContinuousLinearMap.toNormedSpace

theorem normalizedExteriorFunctional_exists_uniform_firstJet :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        HasFDerivAt (normalizedExteriorFunctional parameter power)
          (normalizedExteriorFunctionalDerivative parameter power data) data ∧
        ‖normalizedExteriorFunctionalDerivative parameter power data‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedExteriorFunctionalDerivative parameter power first -
          normalizedExteriorFunctionalDerivative parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ * ‖first - final‖ := by
  obtain ⟨parameterRadius, positive, kernelConstant, kernelOne, kernels⟩ :=
    normalizedExteriorKernelC1_exists_uniform_firstJet
  let constant := 24 * (1 + ‖contourAntiholomorphicTripleCLM‖) * kernelConstant
  have constantOne : 1 ≤ constant := by
    dsimp only [constant]
    nlinarith [norm_nonneg contourAntiholomorphicTripleCLM]
  have firstScalar : 15 * ‖contourAntiholomorphicTripleCLM‖ * kernelConstant ≤ constant := by
    dsimp only [constant]
    nlinarith [mul_nonneg (norm_nonneg contourAntiholomorphicTripleCLM) (by linarith : 0 ≤ kernelConstant)]
  have pairScalar : 23 * ‖contourAntiholomorphicTripleCLM‖ * kernelConstant ≤ constant := by
    dsimp only [constant]
    nlinarith [mul_nonneg (norm_nonneg contourAntiholomorphicTripleCLM) (by linarith : 0 ≤ kernelConstant)]
  refine ⟨parameterRadius, positive, constant, constantOne, ?_⟩
  intro parameter parameterSmall power
  have control := kernels parameter parameterSmall power
  let bound := kernelConstant * (96 : ℝ) ^ (power + 1) * ‖parameter‖
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  constructor
  · intro data dataBound
    have actual := control.1 data dataBound
    refine ⟨hasFDerivAt_normalizedExteriorFunctional parameter power data actual.2.1, ?_⟩
    have derivativeBound := EulerNonuniqueness.General.trilinearKernelDerivative_norm_le
      contourAntiholomorphicTripleCLM (normalizedExteriorKernelC1 parameter power)
      (normalizedExteriorKernelC1Derivative parameter power) data boundNonnegative dataBound actual.1 actual.2.2
    apply derivativeBound.trans
    have scaled := mul_le_mul_of_nonneg_right firstScalar
      (show 0 ≤ (96 : ℝ) ^ (power + 1) * ‖parameter‖ by positivity)
    dsimp only [bound]
    convert scaled using 1 <;> ring
  · intro first final firstBound finalBound
    have firstControl := control.1 first firstBound
    have finalControl := control.1 final finalBound
    have pairControl := control.2 first final firstBound finalBound
    have derivativeBound := EulerNonuniqueness.General.trilinearKernelDerivative_difference_norm_le
      contourAntiholomorphicTripleCLM (normalizedExteriorKernelC1 parameter power)
      (normalizedExteriorKernelC1Derivative parameter power) first final boundNonnegative firstBound finalBound
      firstControl.1 finalControl.1 firstControl.2.2 finalControl.2.2 pairControl.1 pairControl.2
    apply derivativeBound.trans
    have scaled := mul_le_mul_of_nonneg_right pairScalar
      (show 0 ≤ (96 : ℝ) ^ (power + 1) * ‖parameter‖ * ‖first - final‖ by positivity)
    dsimp only [bound]
    convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper
