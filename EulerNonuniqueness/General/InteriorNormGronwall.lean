import EulerNonuniqueness.General.ClosedIntervalODEExtension
import EulerNonuniqueness.General.NormIntegralGronwall

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem norm_constant_forcing_gronwall_of_interior_derivative
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {trajectory velocity : ℝ → Space} {horizon rate forcing : ℝ}
    (horizonPositive : 0 < horizon) (rateNonnegative : 0 ≤ rate) (forcingNonnegative : 0 ≤ forcing)
    (trajectoryContinuous : ContinuousOn trajectory (Icc 0 horizon))
    (velocityContinuous : ContinuousOn velocity (Icc 0 horizon))
    (equation : ∀ time ∈ Ioo 0 horizon, HasDerivAt trajectory (velocity time) time)
    (bound : ∀ time ∈ Ioo 0 horizon, ‖velocity time‖ ≤ rate * ‖trajectory time‖ + forcing) :
    ∀ time ∈ Icc 0 horizon,
      ‖trajectory time‖ ≤ (‖trajectory 0‖ + forcing * time) * Real.exp (rate * time) := by
  obtain ⟨extended, extendedContinuous, agreement, derivative⟩ :=
    exists_closedInterval_ode_extension horizonPositive.le trajectoryContinuous velocityContinuous equation
  have closedBound (time : ℝ) (member : time ∈ Icc 0 horizon) :
      ‖velocity time‖ ≤ rate * ‖trajectory time‖ + forcing := by
    apply ContinuousWithinAt.closure_le
      (s := Ioo (0 : ℝ) horizon)
      (by simpa only [closure_Ioo horizonPositive.ne] using member)
      (((velocityContinuous time member).norm).mono Ioo_subset_Icc_self)
      ((continuousWithinAt_const.mul (trajectoryContinuous time member).norm).add continuousWithinAt_const |>.mono Ioo_subset_Icc_self)
    exact bound
  have estimate := norm_integral_gronwall extendedContinuous continuous_const rateNonnegative horizonPositive.le
    (fun time member => (derivative time ⟨member.1, member.2.le⟩).hasDerivWithinAt)
    (fun time member => by
      rw [agreement ⟨member.1, member.2.le⟩]
      exact closedBound time ⟨member.1, member.2.le⟩)
  intro time member
  have integrandContinuous : Continuous (fun current : ℝ => Real.exp (-rate * current) * forcing) := by fun_prop
  have integralBound : (∫ current in (0 : ℝ)..time, Real.exp (-rate * current) * forcing) ≤ forcing * time := by
    have actual := intervalIntegral.integral_mono_on member.1 (integrandContinuous.intervalIntegrable 0 time)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => forcing) volume 0 time)
      (fun current currentMember => mul_le_of_le_one_left forcingNonnegative
        (Real.exp_le_one_iff.mpr (by nlinarith [currentMember.1])))
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using actual
  have actual := estimate time member
  rw [agreement member, agreement ⟨le_rfl, horizonPositive.le⟩] at actual
  exact actual.trans ((mul_le_mul_of_nonneg_left (add_le_add_left integralBound _) (Real.exp_pos _).le).trans_eq (mul_comm _ _))

end EulerNonuniqueness.General
