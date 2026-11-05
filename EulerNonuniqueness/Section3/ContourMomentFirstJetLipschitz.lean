import EulerNonuniqueness.Section3.NormalizedExteriorFunctionalUniform
import EulerNonuniqueness.Section3.C1PowerFirstJetLipschitz
import EulerNonuniqueness.Section3.ContourPolynomialGaugeMoments
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

def conjugateContourMomentDerivative (degree : ℕ) (data : PeriodicC1HolderHalf) :
    PeriodicC1HolderHalf →L[ℝ] ℂ :=
  EulerNonuniqueness.General.trilinearKernelDerivative contourAntiholomorphicTripleCLM
    (fun current => c1Conjugate (c1NaturalPower current degree))
    (fun current => c1ConjugateCLM.comp (c1NaturalPowerFirstJet current degree)) data

theorem conjugate_contourPolynomialMoment_eq_triple (degree : ℕ) (data : PeriodicC1HolderHalf) :
    star (contourPolynomialMoment degree data) =
      contourAntiholomorphicTripleCLM data (c1Conjugate (c1NaturalPower data degree)) data := by
  rw [contourPolynomialMoment_conjugate_integral, contourAntiholomorphicTripleCLM_apply,
    contourAntiholomorphicPairCLM_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro label _
  change data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label) =
    (data.val.1 label * star ((c1NaturalPower data degree).val.1 label)) * star (data.val.2.val.1 label)
  rw [c1NaturalPower_value, star_pow]

theorem conjugateContourMoment_exists_uniform_firstJet :
    ∃ constant ≥ (1 : ℝ), ∀ degree : ℕ,
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 5 / 2 →
        HasFDerivAt (fun current => star (contourPolynomialMoment degree current))
          (conjugateContourMomentDerivative degree data) data ∧
        ‖conjugateContourMomentDerivative degree data‖ ≤ constant * (96 : ℝ) ^ degree) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 5 / 2 → ‖final‖ ≤ 5 / 2 →
        ‖conjugateContourMomentDerivative degree first - conjugateContourMomentDerivative degree final‖ ≤
          constant * (96 : ℝ) ^ degree * ‖first - final‖ := by
  let constant := 192 * (1 + ‖contourAntiholomorphicTripleCLM‖)
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith [norm_nonneg contourAntiholomorphicTripleCLM]
  have firstScalar : 15 * ‖contourAntiholomorphicTripleCLM‖ * 8 ≤ constant := by
    dsimp only [constant]
    linarith [norm_nonneg contourAntiholomorphicTripleCLM]
  have pairScalar : 23 * ‖contourAntiholomorphicTripleCLM‖ * 8 ≤ constant := by
    dsimp only [constant]
    linarith [norm_nonneg contourAntiholomorphicTripleCLM]
  have conjugateBound : ‖c1ConjugateCLM‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro direction
    simpa only [one_mul] using c1Conjugate_norm_bound direction
  refine ⟨constant, constantOne, ?_⟩
  intro degree
  let kernel := fun data : PeriodicC1HolderHalf => c1Conjugate (c1NaturalPower data degree)
  let kernelDerivative := fun data : PeriodicC1HolderHalf => c1ConjugateCLM.comp (c1NaturalPowerFirstJet data degree)
  let bound := 8 * (96 : ℝ) ^ degree
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have powers24 : (24 : ℝ) ^ degree ≤ (96 : ℝ) ^ degree := pow_le_pow_left₀ (by norm_num) (by norm_num) degree
  have powers48 : (48 : ℝ) ^ degree ≤ (96 : ℝ) ^ degree := pow_le_pow_left₀ (by norm_num) (by norm_num) degree
  have kernelBound (data : PeriodicC1HolderHalf) (small : ‖data‖ ≤ 5 / 2) : ‖kernel data‖ ≤ bound := by
    apply ((c1Conjugate_norm_bound _).trans (c1NaturalPower_norm_bound_twentyFour data (by linarith) degree)).trans
    dsimp only [bound]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) degree]
  have derivativeBound (data : PeriodicC1HolderHalf) (small : ‖data‖ ≤ 5 / 2) : ‖kernelDerivative data‖ ≤ bound := by
    have estimate := (ContinuousLinearMap.opNorm_comp_le c1ConjugateCLM (c1NaturalPowerFirstJet data degree)).trans
      (mul_le_mul conjugateBound (c1NaturalPowerFirstJet_norm_bound data (by linarith) degree) (norm_nonneg _) (by norm_num))
    dsimp only [kernelDerivative, bound]
    apply estimate.trans
    simp only [one_mul]
    linarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) degree]
  have kernelDifference (first final : PeriodicC1HolderHalf) (firstSmall : ‖first‖ ≤ 5 / 2) (finalSmall : ‖final‖ ≤ 5 / 2) :
      ‖kernel first - kernel final‖ ≤ bound * ‖first - final‖ := by
    have estimate := (c1Conjugate_difference_norm_bound _ _).trans
      (c1NaturalPower_difference_geometric_bound first final (by linarith) (by linarith) degree)
    apply estimate.trans
    have scaled := mul_le_mul_of_nonneg_right powers48 (norm_nonneg (first - final))
    dsimp only [bound]
    nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) degree) (norm_nonneg (first - final))]
  have derivativeDifference (first final : PeriodicC1HolderHalf) (firstSmall : ‖first‖ ≤ 5 / 2) (finalSmall : ‖final‖ ≤ 5 / 2) :
      ‖kernelDerivative first - kernelDerivative final‖ ≤ bound * ‖first - final‖ := by
    dsimp only [kernelDerivative]
    rw [← ContinuousLinearMap.comp_sub]
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    have estimate := mul_le_mul conjugateBound
      (c1NaturalPowerFirstJet_difference_geometric_bound first final firstSmall finalSmall degree)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using estimate
  constructor
  · intro data small
    have actualKernel := c1ConjugateCLM.hasFDerivAt.comp data
      (hasFDerivAt_c1NaturalPowerFirstJet data (by linarith) degree)
    have actual := EulerNonuniqueness.General.hasFDerivAt_trilinearKernel contourAntiholomorphicTripleCLM
      kernel kernelDerivative data actualKernel
    have identity : (fun current => star (contourPolynomialMoment degree current)) =
        (fun current => contourAntiholomorphicTripleCLM current (kernel current) current) :=
      funext (conjugate_contourPolynomialMoment_eq_triple degree)
    rw [← identity] at actual
    refine ⟨actual, ?_⟩
    have estimate := EulerNonuniqueness.General.trilinearKernelDerivative_norm_le
      contourAntiholomorphicTripleCLM kernel kernelDerivative data boundNonnegative (by linarith)
      (kernelBound data small) (derivativeBound data small)
    apply estimate.trans
    have scaled := mul_le_mul_of_nonneg_right firstScalar
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) degree)
    dsimp only [bound]
    convert scaled using 1 <;> ring
  · intro first final firstSmall finalSmall
    have estimate := EulerNonuniqueness.General.trilinearKernelDerivative_difference_norm_le
      contourAntiholomorphicTripleCLM kernel kernelDerivative first final boundNonnegative (by linarith) (by linarith)
      (kernelBound first firstSmall) (kernelBound final finalSmall) (derivativeBound first firstSmall)
      (derivativeBound final finalSmall) (kernelDifference first final firstSmall finalSmall)
      (derivativeDifference first final firstSmall finalSmall)
    apply estimate.trans
    have scaled := mul_le_mul_of_nonneg_right pairScalar
      (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 96) degree) (norm_nonneg (first - final)))
    dsimp only [bound]
    convert scaled using 1 <;> ring

theorem conjugateContourMoment_exists_relative_increment :
    ∃ constant ≥ (1 : ℝ), ∀ degree : ℕ,
      ∀ first final initialIncrement finalIncrement : PeriodicC1HolderHalf,
      ‖first‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 5 / 2 →
      ‖final‖ + (‖initialIncrement‖ + ‖finalIncrement‖) ≤ 5 / 2 →
      ‖(star (contourPolynomialMoment degree (first + initialIncrement)) - star (contourPolynomialMoment degree first)) -
        (star (contourPolynomialMoment degree (final + finalIncrement)) - star (contourPolynomialMoment degree final))‖ ≤
        constant * (96 : ℝ) ^ degree * (‖initialIncrement - finalIncrement‖ + ‖first - final‖ * ‖finalIncrement‖) := by
  obtain ⟨constant, one, bounds⟩ := conjugateContourMoment_exists_uniform_firstJet
  refine ⟨constant, one, ?_⟩
  intro degree first final initialIncrement finalIncrement firstInside finalInside
  have actual := bounds degree
  exact EulerNonuniqueness.General.norm_pair_increment_le_of_uniform_firstJet
    (fun current => star (contourPolynomialMoment degree current)) (conjugateContourMomentDerivative degree)
    (by positivity) (fun point member => (actual.1 point (mem_closedBall_zero_iff.mp member)).1)
    (fun point member => (actual.1 point (mem_closedBall_zero_iff.mp member)).2)
    (fun first firstMember final finalMember => actual.2 first final
      (mem_closedBall_zero_iff.mp firstMember) (mem_closedBall_zero_iff.mp finalMember))
    first final initialIncrement finalIncrement firstInside finalInside

end EulerNonuniqueness.Paper
