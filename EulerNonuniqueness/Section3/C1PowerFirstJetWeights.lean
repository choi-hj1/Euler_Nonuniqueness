import EulerNonuniqueness.Section3.C1PowerFirstJet

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

attribute [local instance] powerFirstJetC1Group forcingModeC1RealSpace powerFirstJetOperatorGroup

theorem c1NaturalPowerFirstJet_apply_geometric_bound (data direction : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPowerFirstJet data degree direction‖ ≤ (48 : ℝ) ^ degree * ‖direction‖ := by
  have degreeBound : (degree : ℝ) ≤ (2 : ℝ) ^ degree := by
    exact_mod_cast (Nat.lt_two_pow_self (n := degree)).le
  refine (c1NaturalPowerFirstJet_apply_bound data direction bound degree).trans ?_
  have estimate := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right degreeBound (by positivity : (0 : ℝ) ≤ 24 ^ degree)) (norm_nonneg direction)
  simpa only [← mul_pow, show (2 : ℝ) * 24 = 48 by norm_num] using estimate

theorem c1NaturalPowerFirstJet_norm_bound (data : PeriodicC1HolderHalf)
    (bound : ‖data‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPowerFirstJet data degree‖ ≤ (48 : ℝ) ^ degree := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  exact c1NaturalPowerFirstJet_apply_geometric_bound data direction bound degree

theorem c1NaturalPowerJetError_geometric_bound (first base : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 3) (baseBound : ‖base‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPowerJetError first base degree‖ ≤ (96 : ℝ) ^ degree * ‖first - base‖ ^ 2 := by
  have degreeBound : (degree : ℝ) ≤ (2 : ℝ) ^ degree := by
    exact_mod_cast (Nat.lt_two_pow_self (n := degree)).le
  have squareBound : (degree : ℝ) ^ 2 ≤ (4 : ℝ) ^ degree := by
    calc
      _ ≤ ((2 : ℝ) ^ degree) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg degree) degreeBound 2
      _ = _ := by rw [pow_two, ← mul_pow]; norm_num
  refine (c1NaturalPowerJetError_norm_bound first base firstBound baseBound degree).trans ?_
  have estimate := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right squareBound (by positivity : (0 : ℝ) ≤ 24 ^ degree)) (sq_nonneg ‖first - base‖)
  simpa only [← mul_pow, show (4 : ℝ) * 24 = 96 by norm_num] using estimate

end EulerNonuniqueness.Paper
