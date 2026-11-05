import EulerNonuniqueness.Section3.NormalizedExteriorFunctionalUniform
import EulerNonuniqueness.Section3.NormalizedExteriorQuadraticKernel
import EulerNonuniqueness.General.UniformFirstJetPairIncrement

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace
  antiholomorphicPairOperatorGroup antiholomorphicPairOperatorSpace
  EulerNonuniqueness.General.trilinearKernelBilinearGroup
  EulerNonuniqueness.General.trilinearKernelBilinearSpace
  EulerNonuniqueness.General.trilinearKernelThirdGroup
  EulerNonuniqueness.General.trilinearKernelThirdSpace
  functionalUniformBilinearGroup functionalUniformBilinearSpace
  functionalUniformThirdGroup functionalUniformThirdSeminormedGroup
  functionalUniformThirdSeminormedAddGroup functionalUniformThirdSpace

def normalizedExteriorQuadraticFunctional (parameter : ℂ) (power : ℕ) (data : PeriodicC1HolderHalf) : ℂ :=
  contourAntiholomorphicTripleCLM data (normalizedExteriorQuadraticKernelC1 parameter power data) data

def normalizedExteriorQuadraticFunctionalDerivative (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] ℂ :=
  EulerNonuniqueness.General.trilinearKernelDerivative contourAntiholomorphicTripleCLM
    (normalizedExteriorQuadraticKernelC1 parameter power) (normalizedExteriorQuadraticKernelC1Derivative parameter power) data

theorem normalizedExteriorQuadraticFunctional_exists_uniform_firstJet :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        HasFDerivAt (normalizedExteriorQuadraticFunctional parameter power)
          (normalizedExteriorQuadraticFunctionalDerivative parameter power data) data ∧
        ‖normalizedExteriorQuadraticFunctionalDerivative parameter power data‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedExteriorQuadraticFunctionalDerivative parameter power first -
          normalizedExteriorQuadraticFunctionalDerivative parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 * ‖first - final‖ := by
  obtain ⟨parameterRadius, positive, kernelConstant, kernelOne, kernels⟩ :=
    normalizedExteriorQuadraticKernelC1_exists_uniform_firstJet
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
  let bound := kernelConstant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  constructor
  · intro data dataBound
    have actual := control.1 data dataBound
    have actualDerivative := EulerNonuniqueness.General.hasFDerivAt_trilinearKernel
      contourAntiholomorphicTripleCLM (normalizedExteriorQuadraticKernelC1 parameter power)
      (normalizedExteriorQuadraticKernelC1Derivative parameter power) data actual.2.1
    refine ⟨actualDerivative, ?_⟩
    have estimate := EulerNonuniqueness.General.trilinearKernelDerivative_norm_le
      contourAntiholomorphicTripleCLM (normalizedExteriorQuadraticKernelC1 parameter power)
      (normalizedExteriorQuadraticKernelC1Derivative parameter power) data boundNonnegative dataBound actual.1 actual.2.2
    apply estimate.trans
    have scaled := mul_le_mul_of_nonneg_right firstScalar
      (show 0 ≤ (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 by positivity)
    dsimp only [bound]
    convert scaled using 1 <;> ring
  · intro first final firstBound finalBound
    have firstControl := control.1 first firstBound
    have finalControl := control.1 final finalBound
    have pairControl := control.2 first final firstBound finalBound
    have estimate := EulerNonuniqueness.General.trilinearKernelDerivative_difference_norm_le
      contourAntiholomorphicTripleCLM (normalizedExteriorQuadraticKernelC1 parameter power)
      (normalizedExteriorQuadraticKernelC1Derivative parameter power) first final boundNonnegative firstBound finalBound
      firstControl.1 finalControl.1 firstControl.2.2 finalControl.2.2 pairControl.1 pairControl.2
    apply estimate.trans
    have scaled := mul_le_mul_of_nonneg_right pairScalar
      (show 0 ≤ (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 * ‖first - final‖ by positivity)
    dsimp only [bound]
    convert scaled using 1 <;> ring

theorem normalizedExteriorQuadraticFunctional_exists_relative_increment :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      ∀ first final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖first‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 3 →
      ‖final‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 3 →
        ‖(normalizedExteriorQuadraticFunctional parameter power (first + initialIncrement) -
            normalizedExteriorQuadraticFunctional parameter power first) -
          (normalizedExteriorQuadraticFunctional parameter power (final + finalIncrement) -
            normalizedExteriorQuadraticFunctional parameter power final)‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 *
            (‖initialIncrement - finalIncrement‖ + ‖first - final‖ * ‖finalIncrement‖) := by
  obtain ⟨parameterRadius, positive, constant, one, bounds⟩ :=
    normalizedExteriorQuadraticFunctional_exists_uniform_firstJet
  refine ⟨parameterRadius, positive, constant, one, ?_⟩
  intro parameter small power first final initialIncrement finalIncrement firstInside finalInside
  have actual := bounds parameter small power
  exact EulerNonuniqueness.General.norm_pair_increment_le_of_uniform_firstJet
    (normalizedExteriorQuadraticFunctional parameter power) (normalizedExteriorQuadraticFunctionalDerivative parameter power)
    (by positivity) (fun point member => (actual.1 point (mem_closedBall_zero_iff.mp member)).1)
    (fun point member => (actual.1 point (mem_closedBall_zero_iff.mp member)).2)
    (fun first firstInside final finalInside => actual.2 first final
      (mem_closedBall_zero_iff.mp firstInside) (mem_closedBall_zero_iff.mp finalInside))
    first final initialIncrement finalIncrement firstInside finalInside

end EulerNonuniqueness.Paper
