import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open MeasureTheory Set

namespace EulerNonuniqueness

theorem exponential_volterra_gronwall_on_Icc {trajectory forcing : ℝ → ℝ}
    {initial rate feedback multiplier start finish : ℝ}
    (trajectoryContinuous : ContinuousOn trajectory (Icc start finish))
    (forcingContinuous : ContinuousOn forcing (Icc start finish))
    (feedbackNonnegative : 0 ≤ feedback) (multiplierNonnegative : 0 ≤ multiplier)
    (ordered : start ≤ finish)
    (inequality : ∀ time ∈ Icc start finish,
      trajectory time ≤ initial * Real.exp (rate * (time - start)) +
        multiplier * ∫ current in start..time,
          Real.exp (rate * (time - current)) * (forcing current + feedback * trajectory current)) :
    ∀ time ∈ Icc start finish,
      IntervalIntegrable (fun current => Real.exp (rate * (time - current)) *
        (forcing current + feedback * trajectory current)) volume start time ∧
      IntervalIntegrable (fun current =>
        Real.exp ((rate + multiplier * feedback) * (time - current)) * forcing current) volume start time ∧
      trajectory time ≤ initial * Real.exp ((rate + multiplier * feedback) * (time - start)) +
        multiplier * ∫ current in start..time,
          Real.exp ((rate + multiplier * feedback) * (time - current)) * forcing current := by
  let shiftedTrajectory := fun current => trajectory (current + start)
  let shiftedForcing := fun current => forcing (current + start)
  have shiftedInside (current : ℝ) (inside : current ∈ Icc 0 (finish - start)) :
      current + start ∈ Icc start finish := by constructor <;> linarith only [inside.1, inside.2]
  have shiftedTrajectoryContinuous : ContinuousOn shiftedTrajectory (Icc 0 (finish - start)) :=
    trajectoryContinuous.comp (continuous_id.add continuous_const).continuousOn shiftedInside
  have shiftedForcingContinuous : ContinuousOn shiftedForcing (Icc 0 (finish - start)) :=
    forcingContinuous.comp (continuous_id.add continuous_const).continuousOn shiftedInside
  have integralIdentity (input : ℝ → ℝ) (growth elapsed : ℝ) :
      (∫ current in (0 : ℝ)..elapsed,
        Real.exp (growth * (elapsed - current)) * input (current + start)) =
      ∫ current in start..elapsed + start,
        Real.exp (growth * (elapsed + start - current)) * input current := by
    simpa only [add_sub_add_right_eq_sub, zero_add] using
      intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := elapsed)
        (fun current : ℝ => Real.exp (growth * (elapsed + start - current)) * input current) start
  have shiftedInequality (elapsed : ℝ) (inside : elapsed ∈ Icc 0 (finish - start)) :
      shiftedTrajectory elapsed ≤ initial * Real.exp (rate * elapsed) +
        multiplier * ∫ current in (0 : ℝ)..elapsed,
          Real.exp (rate * (elapsed - current)) *
            (shiftedForcing current + feedback * shiftedTrajectory current) := by
    have actual := inequality (elapsed + start) (shiftedInside elapsed inside)
    dsimp only [shiftedTrajectory, shiftedForcing]
    rw [integralIdentity (fun current => forcing current + feedback * trajectory current)]
    simpa only [add_sub_cancel_right] using actual
  have resolved := exponential_volterra_gronwall shiftedTrajectoryContinuous shiftedForcingContinuous
    feedbackNonnegative multiplierNonnegative (sub_nonneg.mpr ordered) shiftedInequality
  intro time inside
  have prefixSubset : Icc start time ⊆ Icc start finish := Icc_subset_Icc le_rfl inside.2
  have inputContinuous : ContinuousOn (fun current => Real.exp (rate * (time - current)) *
      (forcing current + feedback * trajectory current)) (Icc start time) :=
    (by fun_prop : Continuous (fun current : ℝ => Real.exp (rate * (time - current)))).continuousOn.mul
      ((forcingContinuous.mono prefixSubset).add (continuousOn_const.mul (trajectoryContinuous.mono prefixSubset)))
  have outputContinuous : ContinuousOn (fun current =>
      Real.exp ((rate + multiplier * feedback) * (time - current)) * forcing current) (Icc start time) :=
    (by fun_prop : Continuous (fun current : ℝ =>
      Real.exp ((rate + multiplier * feedback) * (time - current)))).continuousOn.mul (forcingContinuous.mono prefixSubset)
  refine ⟨inputContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1,
    outputContinuous.intervalIntegrable_of_Icc (μ := volume) inside.1, ?_⟩
  have elapsedInside : time - start ∈ Icc 0 (finish - start) :=
    ⟨sub_nonneg.mpr inside.1, sub_le_sub_right inside.2 start⟩
  have actual := resolved (time - start) elapsedInside
  dsimp only [shiftedTrajectory, shiftedForcing] at actual
  rw [integralIdentity forcing (rate + multiplier * feedback) (time - start)] at actual
  simpa only [sub_add_cancel] using actual

end EulerNonuniqueness
