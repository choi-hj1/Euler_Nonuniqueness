import EulerNonuniqueness.Section3.C1PowerGeometricBound

noncomputable section

namespace EulerNonuniqueness.Paper

set_option synthInstance.maxHeartbeats 100000

local instance powerDifferenceC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem c1NaturalPower_difference_bound (first second : PeriodicC1HolderHalf)
    (firstBound : ‖first‖ ≤ 3) (secondBound : ‖second‖ ≤ 3) (degree : ℕ) :
    ‖c1NaturalPower first degree - c1NaturalPower second degree‖ ≤
      degree * (24 : ℝ) ^ degree * ‖first - second‖ := by
  induction degree with
  | zero => simp [c1NaturalPower]
  | succ degree induction =>
      have identity : c1NaturalPower first (degree + 1) - c1NaturalPower second (degree + 1) =
          c1Product first (c1NaturalPower first degree - c1NaturalPower second degree) +
          c1Product (first - second) (c1NaturalPower second degree) := by
        apply PeriodicC1HolderHalf.ext_value
        intro label
        change first.val.1 label * (c1NaturalPower first degree).val.1 label -
          second.val.1 label * (c1NaturalPower second degree).val.1 label =
          first.val.1 label * ((c1NaturalPower first degree).val.1 label -
            (c1NaturalPower second degree).val.1 label) +
          (first.val.1 label - second.val.1 label) * (c1NaturalPower second degree).val.1 label
        ring
      rw [identity]
      calc
        _ ≤ ‖c1Product first (c1NaturalPower first degree - c1NaturalPower second degree)‖ +
            ‖c1Product (first - second) (c1NaturalPower second degree)‖ := norm_add_le _ _
        _ ≤ 8 * ‖first‖ * ‖c1NaturalPower first degree - c1NaturalPower second degree‖ +
            8 * ‖first - second‖ * ‖c1NaturalPower second degree‖ :=
          add_le_add (c1Product_norm_bound _ _) (c1Product_norm_bound _ _)
        _ ≤ 8 * 3 * (degree * (24 : ℝ) ^ degree * ‖first - second‖) +
            8 * ‖first - second‖ * (24 : ℝ) ^ degree := by
          exact add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_left firstBound (by norm_num)) induction
              (norm_nonneg _) (by positivity))
            (mul_le_mul_of_nonneg_left (c1NaturalPower_norm_bound_twentyFour second secondBound degree) (by positivity))
        _ ≤ (degree + 1 : ℕ) * (24 : ℝ) ^ (degree + 1) * ‖first - second‖ := by
          rw [Nat.cast_add, Nat.cast_one, pow_succ]
          nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 24) degree) (norm_nonneg (first - second))]

end EulerNonuniqueness.Paper
