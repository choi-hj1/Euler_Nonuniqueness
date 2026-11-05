import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.Section6

theorem follower_return_bound {envelope source target returned : ℝ → ℝ}
    {initial growth coupling multiplier horizon : ℝ}
    (envelopeContinuous : ContinuousOn envelope (Icc 0 horizon))
    (sourceContinuous : ContinuousOn source (Icc 0 horizon))
    (targetContinuous : ContinuousOn target (Icc 0 horizon))
    (couplingNonnegative : 0 ≤ coupling) (multiplierNonnegative : 0 ≤ multiplier)
    (horizonNonnegative : 0 ≤ horizon)
    (inequality : ∀ time ∈ Icc 0 horizon, envelope time ≤
      multiplier * Real.exp (growth * time) * initial +
        multiplier * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
          (source current + coupling * target current + coupling * envelope current))
    (returnBound : ∀ time ∈ Icc 0 horizon, returned time ≤ coupling * envelope time) :
    ∀ time ∈ Icc 0 horizon, returned time ≤
      multiplier * coupling * Real.exp ((growth + multiplier * coupling) * time) * initial +
        multiplier * coupling * (∫ current in (0 : ℝ)..time,
          Real.exp ((growth + multiplier * coupling) * (time - current)) * source current) +
        multiplier * coupling ^ 2 * (∫ current in (0 : ℝ)..time,
          Real.exp ((growth + multiplier * coupling) * (time - current)) * target current) := by
  have inequality' : ∀ time ∈ Icc 0 horizon, envelope time ≤
      (multiplier * initial) * Real.exp (growth * time) +
        multiplier * ∫ current in (0 : ℝ)..time, Real.exp (growth * (time - current)) *
          ((source current + coupling * target current) + coupling * envelope current) := by
    intro time inside
    convert inequality time inside using 1 <;> ring
  have resolved := exponential_volterra_gronwall envelopeContinuous
    (sourceContinuous.add (continuousOn_const.mul targetContinuous)) couplingNonnegative
    multiplierNonnegative horizonNonnegative inequality'
  intro time inside
  have estimate := (returnBound time inside).trans
    (mul_le_mul_of_nonneg_left (resolved time inside) couplingNonnegative)
  have intervalInside : uIcc (0 : ℝ) time ⊆ Icc 0 horizon := by
    rw [uIcc_of_le inside.1]
    exact Icc_subset_Icc le_rfl inside.2
  have exponentialContinuous : ContinuousOn
      (fun current => Real.exp ((growth + multiplier * coupling) * (time - current))) (uIcc 0 time) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  have sourceIntegrable : IntervalIntegrable (fun current =>
      Real.exp ((growth + multiplier * coupling) * (time - current)) * source current) volume 0 time :=
    (exponentialContinuous.mul (sourceContinuous.mono intervalInside)).intervalIntegrable
  have targetIntegrable : IntervalIntegrable (fun current =>
      Real.exp ((growth + multiplier * coupling) * (time - current)) * target current) volume 0 time :=
    (exponentialContinuous.mul (targetContinuous.mono intervalInside)).intervalIntegrable
  have split : (∫ current in (0 : ℝ)..time,
      Real.exp ((growth + multiplier * coupling) * (time - current)) *
        (source current + coupling * target current)) =
      (∫ current in (0 : ℝ)..time, Real.exp ((growth + multiplier * coupling) * (time - current)) * source current) +
        coupling * ∫ current in (0 : ℝ)..time,
          Real.exp ((growth + multiplier * coupling) * (time - current)) * target current := by
    simp_rw [mul_add, mul_left_comm _ coupling]
    rw [intervalIntegral.integral_add sourceIntegrable (targetIntegrable.const_mul coupling),
      intervalIntegral.integral_const_mul]
  rw [split] at estimate
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
