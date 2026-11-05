import EulerNonuniqueness.Section3.NormalizedExteriorKernelZeroJet
import EulerNonuniqueness.Section3.NormalizedExteriorKernelUniform

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

def normalizedExteriorQuadraticKernelC1 (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf :=
  normalizedExteriorKernelC1 parameter power data - normalizedExteriorKernelC1Derivative parameter power 0 data

def normalizedExteriorQuadraticKernelC1Derivative (parameter : ℂ) (power : ℕ)
    (data : PeriodicC1HolderHalf) : PeriodicC1HolderHalf →L[ℝ] PeriodicC1HolderHalf :=
  normalizedExteriorKernelC1Derivative parameter power data - normalizedExteriorKernelC1Derivative parameter power 0

theorem normalizedExteriorQuadraticKernelC1_zero (parameter : ℂ) (power : ℕ) :
    normalizedExteriorQuadraticKernelC1 parameter power 0 = 0 := by
  rw [normalizedExteriorQuadraticKernelC1, normalizedExteriorKernelC1_zero, map_zero, sub_zero]

theorem normalizedExteriorQuadraticKernelC1_exists_uniform_firstJet :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        ‖normalizedExteriorQuadraticKernelC1 parameter power data‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 ∧
        HasFDerivAt (normalizedExteriorQuadraticKernelC1 parameter power)
          (normalizedExteriorQuadraticKernelC1Derivative parameter power data) data ∧
        ‖normalizedExteriorQuadraticKernelC1Derivative parameter power data‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedExteriorQuadraticKernelC1 parameter power first -
          normalizedExteriorQuadraticKernelC1 parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 * ‖first - final‖ ∧
        ‖normalizedExteriorQuadraticKernelC1Derivative parameter power first -
          normalizedExteriorQuadraticKernelC1Derivative parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2 * ‖first - final‖ := by
  obtain ⟨actualRadius, actualPositive, actualConstant, actualOne, actualBound⟩ :=
    normalizedExteriorKernelC1_exists_uniform_bounds
  obtain ⟨pairRadius, pairPositive, constant, one, pairBound⟩ :=
    normalizedExteriorKernelC1_exists_uniform_derivative_difference
  refine ⟨min actualRadius pairRadius, lt_min actualPositive pairPositive, 9 * constant, by linarith, ?_⟩
  intro parameter small power
  have actualSmall := small.trans (min_le_left _ _)
  have pairSmall := small.trans (min_le_right _ _)
  let bound := constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ^ 2
  have boundNonnegative : 0 ≤ bound := by dsimp only [bound]; positivity
  have actual (data : PeriodicC1HolderHalf) (dataBound : ‖data‖ ≤ 3) :
      HasFDerivAt (normalizedExteriorQuadraticKernelC1 parameter power)
        (normalizedExteriorQuadraticKernelC1Derivative parameter power data) data :=
    ((actualBound parameter actualSmall power data dataBound).2.1).sub
      (normalizedExteriorKernelC1Derivative parameter power 0).hasFDerivAt
  have derivativeBound (data : PeriodicC1HolderHalf) (dataBound : ‖data‖ ≤ 3) :
      ‖normalizedExteriorQuadraticKernelC1Derivative parameter power data‖ ≤ 3 * bound := by
    have estimate := pairBound parameter pairSmall power data 0 dataBound (by simp)
    simp only [sub_zero] at estimate
    exact estimate.trans ((mul_le_mul_of_nonneg_left dataBound boundNonnegative).trans_eq (by ring))
  have functionLip : LipschitzOnWith ⟨3 * bound, by positivity⟩
      (normalizedExteriorQuadraticKernelC1 parameter power) (closedBall (0 : PeriodicC1HolderHalf) 3) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := normalizedExteriorQuadraticKernelC1Derivative parameter power)
      (fun data member => (actual data (mem_closedBall_zero_iff.mp member)).hasFDerivWithinAt) _
      (convex_closedBall _ _)
    intro data member
    change ‖normalizedExteriorQuadraticKernelC1Derivative parameter power data‖ ≤ 3 * bound
    exact derivativeBound data (mem_closedBall_zero_iff.mp member)
  constructor
  · intro data dataBound
    have estimate := functionLip.norm_sub_le (mem_closedBall_zero_iff.mpr dataBound)
      (mem_closedBall_zero_iff.mpr (by simp : ‖(0 : PeriodicC1HolderHalf)‖ ≤ 3))
    simp only [normalizedExteriorQuadraticKernelC1_zero, sub_zero, NNReal.coe_mk] at estimate
    have valueBound := estimate.trans (mul_le_mul_of_nonneg_left dataBound (by positivity : 0 ≤ 3 * bound))
    refine ⟨valueBound.trans_eq (by dsimp only [bound]; ring), actual data dataBound, ?_⟩
    have estimate := derivativeBound data dataBound
    exact estimate.trans ((mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 9)
      boundNonnegative).trans_eq (by dsimp only [bound]; ring))
  · intro first final firstBound finalBound
    have estimate := functionLip.norm_sub_le (mem_closedBall_zero_iff.mpr firstBound)
      (mem_closedBall_zero_iff.mpr finalBound)
    simp only [NNReal.coe_mk] at estimate
    refine ⟨estimate.trans ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 9) boundNonnegative)
        (norm_nonneg (first - final))).trans_eq (by dsimp only [bound]; ring)
    · have estimate := pairBound parameter pairSmall power first final firstBound finalBound
      have identity : normalizedExteriorQuadraticKernelC1Derivative parameter power first -
          normalizedExteriorQuadraticKernelC1Derivative parameter power final =
          normalizedExteriorKernelC1Derivative parameter power first - normalizedExteriorKernelC1Derivative parameter power final := by
        unfold normalizedExteriorQuadraticKernelC1Derivative
        abel
      rw [identity]
      have scaleBound := mul_le_mul_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 9)
        (mul_nonneg boundNonnegative (norm_nonneg (first - final)))
      calc
        _ ≤ bound * ‖first - final‖ := estimate
        _ ≤ 9 * (bound * ‖first - final‖) := by simpa only [one_mul] using scaleBound
        _ = _ := by dsimp only [bound] <;> ring

end EulerNonuniqueness.Paper
