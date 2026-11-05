import EulerNonuniqueness.Section6.IntegrableUnstableDuhamel

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem unstable_departure_of_weighted_coefficients {trajectory : ℝ → ℝ}
    {rate scale coefficient threshold earlyBound earlyTime horizon : ℝ}
    (continuous : ContinuousOn trajectory (Icc 0 horizon))
    (ratePositive : 0 < rate) (scalePositive : 0 < scale) (coefficientPositive : 0 < coefficient)
    (thresholdPositive : 0 < threshold) (earlyBoundNonnegative : 0 ≤ earlyBound)
    (earlyTimeNonnegative : 0 ≤ earlyTime) (earlyTimeBound : earlyTime ≤ horizon)
    (earlySmall : scale * earlyBound * Real.exp (rate * earlyTime) < threshold)
    (finalLarge : 4 * threshold ≤ scale * coefficient * Real.exp (rate * horizon))
    (early : ∀ time ∈ Icc 0 earlyTime, |Real.exp (-rate * time) * trajectory time| ≤ scale * earlyBound)
    (late : ∀ time ∈ Icc earlyTime horizon,
      |Real.exp (-rate * time) * trajectory time - scale * coefficient| ≤ scale * coefficient / 2) :
    (∀ time ∈ Icc 0 horizon, -threshold < trajectory time) ∧
      ∃ time ∈ Icc 0 horizon, earlyTime < time ∧ trajectory time = threshold := by
  classical
  have reconstruction (time : ℝ) : trajectory time =
      Real.exp (rate * time) * (Real.exp (-rate * time) * trajectory time) := by
    rw [← mul_assoc, ← Real.exp_add]
    ring_nf
    simp only [Real.exp_zero, one_mul]
  have earlyEstimate (time : ℝ) (inside : time ∈ Icc 0 earlyTime) : |trajectory time| < threshold := by
    calc
      _ = |Real.exp (rate * time) * (Real.exp (-rate * time) * trajectory time)| :=
        congrArg abs (reconstruction time)
      _ = Real.exp (rate * time) * |Real.exp (-rate * time) * trajectory time| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (rate * time) * (scale * earlyBound) :=
        mul_le_mul_of_nonneg_left (early time inside) (Real.exp_pos _).le
      _ ≤ Real.exp (rate * earlyTime) * (scale * earlyBound) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left inside.2 ratePositive.le)) (mul_nonneg scalePositive.le earlyBoundNonnegative)
      _ < threshold := by nlinarith [earlySmall]
  have lateEstimate (time : ℝ) (inside : time ∈ Icc earlyTime horizon) :
      scale * coefficient / 2 * Real.exp (rate * time) ≤ trajectory time := by
    have coefficientLower := (abs_le.mp (late time inside)).1
    rw [reconstruction time]
    nlinarith [mul_le_mul_of_nonneg_left coefficientLower (Real.exp_pos (rate * time)).le]
  constructor
  · intro time inside
    by_cases earlyInside : time ≤ earlyTime
    · exact (abs_lt.mp (earlyEstimate time ⟨inside.1, earlyInside⟩)).1
    · have lower := lateEstimate time ⟨(le_of_not_ge earlyInside), inside.2⟩
      have positive : 0 < scale * coefficient / 2 * Real.exp (rate * time) := by positivity
      linarith
  · have initialBelow : trajectory 0 < threshold :=
      (abs_lt.mp (earlyEstimate 0 ⟨le_rfl, earlyTimeNonnegative⟩)).2
    have finalAbove : threshold < trajectory horizon := by
      have lower := lateEstimate horizon ⟨earlyTimeBound, le_rfl⟩
      nlinarith [Real.exp_pos (rate * horizon)]
    obtain ⟨time, inside, equal⟩ := intermediate_value_Icc
      (earlyTimeNonnegative.trans earlyTimeBound) continuous
      (show threshold ∈ Icc (trajectory 0) (trajectory horizon) from ⟨initialBelow.le, finalAbove.le⟩)
    refine ⟨time, inside, ?_, equal⟩
    by_contra notLate
    have estimate := earlyEstimate time ⟨inside.1, le_of_not_gt notLate⟩
    rw [equal, abs_of_pos thresholdPositive] at estimate
    exact (lt_irrefl threshold) estimate

end EulerNonuniqueness.Section6
