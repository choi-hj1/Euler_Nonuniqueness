import Mathlib

noncomputable section

open Set

namespace EulerNonuniqueness

theorem exists_attained_exponential_majorant {function : ℝ → ℝ} {rate horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon) (continuous : ContinuousOn function (Icc 0 horizon))
    (nonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ function time) :
    ∃ bound : ℝ, 0 ≤ bound ∧ (∀ time ∈ Icc 0 horizon, function time ≤ bound * Real.exp (rate * time)) ∧
      ∃ time ∈ Icc 0 horizon, function time = bound * Real.exp (rate * time) := by
  let weighted := fun time => Real.exp (-rate * time) * function time
  have weightedContinuous : ContinuousOn weighted (Icc 0 horizon) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul continuous
  obtain ⟨maximumTime, inside, maximal⟩ := isCompact_Icc.exists_isMaxOn
    ⟨0, le_rfl, horizonNonnegative⟩ weightedContinuous
  have cancellation (time : ℝ) : Real.exp (rate * time) * Real.exp (-rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  refine ⟨weighted maximumTime, mul_nonneg (Real.exp_pos _).le (nonnegative maximumTime inside), ?_, maximumTime, inside, ?_⟩
  · intro time timeInside
    have estimate := mul_le_mul_of_nonneg_left (maximal timeInside) (Real.exp_pos (rate * time)).le
    change Real.exp (rate * time) * (Real.exp (-rate * time) * function time) ≤ _ at estimate
    rw [← mul_assoc, cancellation, one_mul] at estimate
    simpa only [mul_comm] using estimate
  · dsimp only [weighted]
    calc
      _ = function maximumTime * (Real.exp (rate * maximumTime) * Real.exp (-rate * maximumTime)) := by rw [cancellation, mul_one]
      _ = _ := by ring

end EulerNonuniqueness
