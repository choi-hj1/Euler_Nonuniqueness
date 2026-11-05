import EulerNonuniqueness.Section3.C1PowerFirstJetWeights
import EulerNonuniqueness.General.UniformQuadraticFirstJetLipschitz

noncomputable section

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup

theorem c1NaturalPower_difference_geometric_bound (first final : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 3) (finalBound : ‖final‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPower first degree - c1NaturalPower final degree‖ ≤
      (48 : ℝ) ^ degree * ‖first - final‖ := by
  have degreeBound : (degree : ℝ) ≤ (2 : ℝ) ^ degree := by
    exact_mod_cast (Nat.lt_two_pow_self (n := degree)).le
  have actual := c1NaturalPower_difference_bound first final firstBound finalBound degree
  apply actual.trans
  have scaled := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right degreeBound
    (by positivity : 0 ≤ (24 : ℝ) ^ degree)) (norm_nonneg (first - final))
  simpa only [← mul_pow, show (2 : ℝ) * 24 = 48 by norm_num] using scaled

theorem c1NaturalPowerFirstJet_difference_geometric_bound (first final : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 5 / 2) (finalBound : ‖final‖ ≤ 5 / 2) (degree : ℕ) :
    ‖c1NaturalPowerFirstJet first degree - c1NaturalPowerFirstJet final degree‖ ≤
      8 * (96 : ℝ) ^ degree * ‖first - final‖ := by
  let constant := (96 : ℝ) ^ degree
  have nonnegative : 0 ≤ constant := by positivity
  have firstThree : ‖first‖ ≤ 3 := by linarith
  have finalThree : ‖final‖ ≤ 3 := by linarith
  by_cases close : 2 * ‖first - final‖ ≤ 1 / 2
  · have taylor (base : PeriodicC1HolderHalf) (bound : ‖base‖ ≤ 5 / 2)
        (increment : PeriodicC1HolderHalf) (small : ‖increment‖ ≤ 1 / 2) :
        ‖EulerNonuniqueness.General.linearJetTaylorError
          (fun data => c1NaturalPower data degree) (fun data => c1NaturalPowerFirstJet data degree)
          base increment‖ ≤ constant * ‖increment‖ ^ 2 := by
      have shifted : ‖base + increment‖ ≤ 3 := (norm_add_le _ _).trans (by linarith)
      have actual := c1NaturalPowerJetError_geometric_bound (base + increment) base shifted
        (by linarith) degree
      simpa only [EulerNonuniqueness.General.linearJetTaylorError, c1NaturalPowerJetError,
        add_sub_cancel_left] using actual
    have actual := EulerNonuniqueness.General.linear_operator_difference_le_of_uniform_quadratic
      (fun data => c1NaturalPower data degree) (fun data => c1NaturalPowerFirstJet data degree)
      final first nonnegative (taylor final finalBound) (taylor first firstBound) close
    exact actual.trans (by nlinarith [mul_nonneg nonnegative (norm_nonneg (first - final))])
  · have powers : (48 : ℝ) ^ degree ≤ (96 : ℝ) ^ degree :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) degree
    have firstJet := (c1NaturalPowerFirstJet_norm_bound first firstThree degree).trans powers
    have finalJet := (c1NaturalPowerFirstJet_norm_bound final finalThree degree).trans powers
    have triangle := (norm_sub_le (c1NaturalPowerFirstJet first degree)
      (c1NaturalPowerFirstJet final degree)).trans (add_le_add firstJet finalJet)
    have scaled := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge close)) nonnegative
    dsimp only [constant] at *
    nlinarith

end EulerNonuniqueness.Paper
