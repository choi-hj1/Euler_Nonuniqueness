import EulerNonuniqueness.General.IntegralGronwall

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem exponential_volterra_gronwall {trajectory forcing : ℝ → ℝ}
    {initial rate feedback multiplier horizon : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (feedbackNonnegative : 0 ≤ feedback) (multiplierNonnegative : 0 ≤ multiplier)
    (horizonNonnegative : 0 ≤ horizon)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (rate * (time - current)) * (forcing current + feedback * trajectory current)) :
    ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial * Real.exp ((rate + multiplier * feedback) * time) +
      multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp ((rate + multiplier * feedback) * (time - current)) * forcing current := by
  let weightedTrajectory := fun time => Real.exp (-rate * time) * trajectory time
  let weightedForcing := fun time => multiplier * Real.exp (-rate * time) * forcing time
  have exponentialIdentity (time current : ℝ) :
      Real.exp (-rate * time) * Real.exp (rate * (time - current)) = Real.exp (-rate * current) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have cancellation (time : ℝ) : Real.exp (-rate * time) * Real.exp (rate * time) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have weightedInequality : ∀ time ∈ Icc 0 horizon, weightedTrajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, weightedForcing current + multiplier * feedback * weightedTrajectory current := by
    intro time inside
    have estimate := mul_le_mul_of_nonneg_left (inequality time inside) (Real.exp_pos (-rate * time)).le
    have identity : Real.exp (-rate * time) * (initial * Real.exp (rate * time) +
        multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp (rate * (time - current)) * (forcing current + feedback * trajectory current)) =
        initial + ∫ current in (0 : ℝ)..time,
          weightedForcing current + multiplier * feedback * weightedTrajectory current := by
      rw [mul_add]
      have firstTerm : Real.exp (-rate * time) * (initial * Real.exp (rate * time)) = initial := by
        rw [mul_left_comm, cancellation, mul_one]
      rw [firstTerm, ← mul_assoc, ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [weightedForcing, weightedTrajectory]
      calc
        _ = multiplier * (Real.exp (-rate * time) * Real.exp (rate * (time - current))) *
            (forcing current + feedback * trajectory current) := by ring
        _ = _ := by rw [exponentialIdentity]; ring
    rw [identity] at estimate
    exact estimate
  have weightedBound := integral_gronwall_with_forcing_on_Icc
    (trajectory := weightedTrajectory) (forcing := weightedForcing)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul trajectoryContinuous)
    ((continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn.mul forcingContinuous)
    (mul_nonneg multiplierNonnegative feedbackNonnegative) horizonNonnegative weightedInequality
  intro time inside
  have estimate := mul_le_mul_of_nonneg_left (weightedBound time inside) (Real.exp_pos (rate * time)).le
  have trajectoryIdentity : Real.exp (rate * time) * weightedTrajectory time = trajectory time := by
    dsimp only [weightedTrajectory]
    rw [← mul_assoc, mul_comm (Real.exp (rate * time)), cancellation, one_mul]
  rw [trajectoryIdentity] at estimate
  have identity : Real.exp (rate * time) * (Real.exp (multiplier * feedback * time) *
      (initial + ∫ current in (0 : ℝ)..time,
        Real.exp (-(multiplier * feedback) * current) * weightedForcing current)) =
      initial * Real.exp ((rate + multiplier * feedback) * time) +
        multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp ((rate + multiplier * feedback) * (time - current)) * forcing current := by
    have combined : Real.exp (rate * time) * Real.exp (multiplier * feedback * time) =
        Real.exp ((rate + multiplier * feedback) * time) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, combined, mul_add, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    congr 1
    · ring
    · apply intervalIntegral.integral_congr
      intro current _
      dsimp only [weightedForcing]
      have combinedInput : Real.exp ((rate + multiplier * feedback) * time) *
          Real.exp (-(multiplier * feedback) * current) * Real.exp (-rate * current) =
          Real.exp ((rate + multiplier * feedback) * (time - current)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      calc
        _ = multiplier * (Real.exp ((rate + multiplier * feedback) * time) *
          Real.exp (-(multiplier * feedback) * current) * Real.exp (-rate * current)) * forcing current := by ring
        _ = _ := by rw [combinedInput]; ring
  rw [identity] at estimate
  exact estimate

end EulerNonuniqueness
