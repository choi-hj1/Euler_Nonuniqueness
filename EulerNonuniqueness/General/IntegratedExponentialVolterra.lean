import EulerNonuniqueness.General.IntegratedCoefficientGronwall

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness.General

theorem exponential_volterra_of_integrated_coefficient_on_Icc
    {trajectory forcing coefficient : ℝ → ℝ} {initial rate multiplier horizon : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (coefficientContinuous : ContinuousOn coefficient (Icc 0 horizon))
    (horizonNonnegative : 0 ≤ horizon) (multiplierNonnegative : 0 ≤ multiplier)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (coefficientNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ coefficient time)
    (inequality : ∀ time ∈ Icc 0 horizon, trajectory time ≤ initial * Real.exp (rate * time) +
      multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
        (forcing current + coefficient current * trajectory current)) :
    ∀ time ∈ Icc 0 horizon, Real.exp (-rate * time) * trajectory time ≤
      Real.exp (multiplier * ∫ current in (0 : ℝ)..time, coefficient current) *
        (initial + multiplier * ∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing current) := by
  let weightedTrajectory := fun time => Real.exp (-rate * time) * trajectory time
  let weightedForcing := fun time => multiplier * (Real.exp (-rate * time) * forcing time)
  let weightedCoefficient := fun time => multiplier * coefficient time
  have exponentialContinuous : Continuous (fun time : ℝ => Real.exp (-rate * time)) := by fun_prop
  have exponentialIdentity (time current : ℝ) :
      Real.exp (-rate * time) * Real.exp (rate * (time - current)) = Real.exp (-rate * current) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have cancellation (time : ℝ) : Real.exp (-rate * time) * Real.exp (rate * time) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have weightedInequality : ∀ time ∈ Icc 0 horizon, weightedTrajectory time ≤ initial +
      ∫ current in (0 : ℝ)..time, weightedForcing current + weightedCoefficient current * weightedTrajectory current := by
    intro time inside
    have multiplied := mul_le_mul_of_nonneg_left (inequality time inside) (Real.exp_pos (-rate * time)).le
    have identity : Real.exp (-rate * time) * (initial * Real.exp (rate * time) +
        multiplier * ∫ current in (0 : ℝ)..time, Real.exp (rate * (time - current)) *
          (forcing current + coefficient current * trajectory current)) =
        initial + ∫ current in (0 : ℝ)..time,
          weightedForcing current + weightedCoefficient current * weightedTrajectory current := by
      rw [mul_add]
      have initialIdentity : Real.exp (-rate * time) * (initial * Real.exp (rate * time)) = initial := by
        rw [mul_left_comm, cancellation, mul_one]
      rw [initialIdentity, ← mul_assoc, ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro current _
      dsimp only [weightedForcing, weightedCoefficient, weightedTrajectory]
      calc
        _ = multiplier * (Real.exp (-rate * time) * Real.exp (rate * (time - current))) *
          (forcing current + coefficient current * trajectory current) := by ring
        _ = _ := by rw [exponentialIdentity]; ring
    rw [identity] at multiplied
    exact multiplied
  have bound := integral_gronwall_of_integrated_coefficient_on_Icc
    (exponentialContinuous.continuousOn.mul trajectoryContinuous)
    (continuousOn_const.mul (exponentialContinuous.continuousOn.mul forcingContinuous))
    (continuousOn_const.mul coefficientContinuous) horizonNonnegative
    (fun time inside => mul_nonneg multiplierNonnegative
      (mul_nonneg (Real.exp_pos _).le (forcingNonnegative time inside)))
    (fun time inside => mul_nonneg multiplierNonnegative (coefficientNonnegative time inside))
    weightedInequality
  intro time inside
  simpa only [weightedTrajectory, weightedForcing, weightedCoefficient, intervalIntegral.integral_const_mul]
    using bound time inside

end EulerNonuniqueness.General
