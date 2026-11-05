import EulerNonuniqueness.Section3.NormalizedExteriorKernelC1Relative

noncomputable section

open Metric

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace
  c1InverseAnalyticOperatorGroup c1InverseAnalyticOperatorSpace

theorem normalizedExteriorKernelC1_exists_uniform_firstJet :
    ∃ parameterRadius > (0 : ℝ), ∃ constant ≥ (1 : ℝ),
      ∀ parameter : ℂ, ‖parameter‖ ≤ parameterRadius → ∀ power : ℕ,
      (∀ data : PeriodicC1HolderHalf, ‖data‖ ≤ 3 →
        ‖normalizedExteriorKernelC1 parameter power data‖ ≤ constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ∧
        HasFDerivAt (normalizedExteriorKernelC1 parameter power)
          (normalizedExteriorKernelC1Derivative parameter power data) data ∧
        ‖normalizedExteriorKernelC1Derivative parameter power data‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖) ∧
      ∀ first final : PeriodicC1HolderHalf, ‖first‖ ≤ 3 → ‖final‖ ≤ 3 →
        ‖normalizedExteriorKernelC1 parameter power first - normalizedExteriorKernelC1 parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ * ‖first - final‖ ∧
        ‖normalizedExteriorKernelC1Derivative parameter power first -
          normalizedExteriorKernelC1Derivative parameter power final‖ ≤
          constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ * ‖first - final‖ := by
  obtain ⟨valueRadius, valuePositive, valueConstant, valueOne, values⟩ :=
    normalizedExteriorKernelC1_exists_uniform_bounds
  obtain ⟨derivativeRadius, derivativePositive, derivativeConstant, derivativeOne, derivatives⟩ :=
    normalizedExteriorKernelC1_exists_uniform_derivative_difference
  let parameterRadius := min valueRadius (min derivativeRadius 1)
  let constant := valueConstant + derivativeConstant
  have constantOne : 1 ≤ constant := by dsimp only [constant]; linarith
  have valueLe : valueConstant ≤ constant := by dsimp only [constant]; linarith
  have derivativeLe : derivativeConstant ≤ constant := by dsimp only [constant]; linarith
  refine ⟨parameterRadius, by dsimp only [parameterRadius]; positivity, constant, constantOne, ?_⟩
  intro parameter parameterSmall power
  have valueSmall : ‖parameter‖ ≤ valueRadius := parameterSmall.trans (min_le_left _ _)
  have derivativeSmall : ‖parameter‖ ≤ derivativeRadius :=
    parameterSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have parameterOne : ‖parameter‖ ≤ 1 :=
    parameterSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have parameterSquare : ‖parameter‖ ^ 2 ≤ ‖parameter‖ := by nlinarith [norm_nonneg parameter]
  have powers : (48 : ℝ) ^ (power + 1) ≤ (96 : ℝ) ^ (power + 1) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have controls (data : PeriodicC1HolderHalf) (bounded : ‖data‖ ≤ 3) :
      ‖normalizedExteriorKernelC1 parameter power data‖ ≤ constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ ∧
      HasFDerivAt (normalizedExteriorKernelC1 parameter power)
        (normalizedExteriorKernelC1Derivative parameter power data) data ∧
      ‖normalizedExteriorKernelC1Derivative parameter power data‖ ≤
        constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ := by
    have actual := values parameter valueSmall power data bounded
    have scalar : valueConstant * (48 : ℝ) ^ (power + 1) * ‖parameter‖ ≤
        constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖ := by gcongr
    exact ⟨actual.1.trans scalar, actual.2.1, actual.2.2.trans scalar⟩
  refine ⟨controls, ?_⟩
  intro first final firstBound finalBound
  have functionLip : LipschitzOnWith
      ⟨constant * (96 : ℝ) ^ (power + 1) * ‖parameter‖, by positivity⟩
      (normalizedExteriorKernelC1 parameter power) (closedBall (0 : PeriodicC1HolderHalf) 3) := by
    apply Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (f' := normalizedExteriorKernelC1Derivative parameter power)
      (fun point member => ((controls point (mem_closedBall_zero_iff.mp member)).2.1).hasFDerivWithinAt)
      _ (convex_closedBall _ _)
    intro point member
    exact_mod_cast (controls point (mem_closedBall_zero_iff.mp member)).2.2
  refine ⟨functionLip.norm_sub_le (mem_closedBall_zero_iff.mpr firstBound)
    (mem_closedBall_zero_iff.mpr finalBound), ?_⟩
  have actual := derivatives parameter derivativeSmall power first final firstBound finalBound
  apply actual.trans
  gcongr

end EulerNonuniqueness.Paper
