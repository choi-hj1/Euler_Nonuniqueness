import Mathlib

noncomputable section

namespace EulerNonuniqueness.General

variable {Domain Range : Type*}
  [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

def linearJetTaylorError (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (base increment : Domain) : Range := function (base + increment) - function base - linear base increment

theorem linearJetTaylorError_difference_identity (function : Domain → Range)
    (linear : Domain → Domain →L[ℝ] Range) (first second step : Domain) :
    (linear second - linear first) step =
      linearJetTaylorError function linear first ((second - first) + step) -
        linearJetTaylorError function linear first (second - first) -
          linearJetTaylorError function linear second step := by
  have plus : first + ((second - first) + step) = second + step := by abel
  have center : first + (second - first) = second := by abel
  unfold linearJetTaylorError
  rw [plus, center]
  simp only [map_add, map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem linear_operator_difference_le_of_uniform_quadratic
    (function : Domain → Range) (linear : Domain → Domain →L[ℝ] Range)
    (first second : Domain) {constant incrementRadius : ℝ} (nonnegative : 0 ≤ constant)
    (firstTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖linearJetTaylorError function linear first increment‖ ≤ constant * ‖increment‖ ^ 2)
    (secondTaylor : ∀ increment, ‖increment‖ ≤ incrementRadius →
      ‖linearJetTaylorError function linear second increment‖ ≤ constant * ‖increment‖ ^ 2)
    (close : 2 * ‖second - first‖ ≤ incrementRadius) :
    ‖linear second - linear first‖ ≤ 6 * constant * ‖second - first‖ := by
  by_cases equal : first = second
  · subst second
    simp
  let distance := ‖second - first‖
  have distancePositive : 0 < distance := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm equal))
  have distanceSmall : distance ≤ incrementRadius := by
    dsimp only [distance]
    nlinarith [norm_nonneg (second - first)]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro direction directionNorm
  let step := distance • direction
  have stepNorm : ‖step‖ = distance := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos distancePositive, directionNorm, mul_one]
  have plusNorm : ‖(second - first) + step‖ ≤ 2 * distance := by
    have bound := norm_add_le (second - first) step
    rw [stepNorm] at bound
    dsimp only [distance] at *
    linarith
  have plusError : ‖linearJetTaylorError function linear first ((second - first) + step)‖ ≤
      constant * (2 * distance) ^ 2 :=
    (firstTaylor _ (plusNorm.trans close)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) plusNorm 2) nonnegative)
  have centerError : ‖linearJetTaylorError function linear first (second - first)‖ ≤
      constant * distance ^ 2 := firstTaylor _ distanceSmall
  have finalError : ‖linearJetTaylorError function linear second step‖ ≤ constant * distance ^ 2 := by
    have estimate := secondTaylor step (stepNorm.le.trans distanceSmall)
    simpa only [stepNorm] using estimate
  have errorBound : ‖(linear second - linear first) step‖ ≤ 6 * constant * distance ^ 2 := by
    rw [linearJetTaylorError_difference_identity function linear first second step]
    have triangle := (norm_sub_le
      (linearJetTaylorError function linear first ((second - first) + step) -
        linearJetTaylorError function linear first (second - first))
      (linearJetTaylorError function linear second step)).trans
        (add_le_add_right (norm_sub_le _ _) _)
    nlinarith
  have scaled : (linear second - linear first) step =
      distance • ((linear second - linear first) direction) := by
    exact (linear second - linear first).map_smul distance direction
  rw [scaled, norm_smul, Real.norm_eq_abs, abs_of_pos distancePositive] at errorBound
  have rightEquality : 6 * constant * distance ^ 2 = distance * (6 * constant * distance) := by ring
  rw [rightEquality] at errorBound
  exact (mul_le_mul_left distancePositive).mp errorBound

end EulerNonuniqueness.General
