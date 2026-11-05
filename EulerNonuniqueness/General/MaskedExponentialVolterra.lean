import EulerNonuniqueness.General.ExponentialVolterra

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem norm_masked_exponential_volterra_le
    {Index : Type*} [Fintype Index] [DecidableEq Index] (selected : Finset Index)
    {states inputs : Index → ℝ → ℝ} {forcing : ℝ → ℝ}
    {rates : Index → ℝ} {growth multiplier horizon : ℝ}
    (inputsContinuous : ∀ index ∈ selected, ContinuousOn (inputs index) (Icc 0 horizon))
    (forcingContinuous : ContinuousOn forcing (Icc 0 horizon))
    (multiplierNonnegative : 0 ≤ multiplier)
    (statesNonnegative : ∀ index ∈ selected, ∀ time ∈ Icc 0 horizon, 0 ≤ states index time)
    (forcingNonnegative : ∀ time ∈ Icc 0 horizon, 0 ≤ forcing time)
    (ratesBound : ∀ index ∈ selected, rates index ≤ growth)
    (inputBound : ∀ index ∈ selected, ∀ time ∈ Icc 0 horizon, inputs index time ≤ forcing time)
    (propagator : ∀ index ∈ selected, ∀ time ∈ Icc 0 horizon,
      states index time ≤ multiplier * ∫ current in (0 : ℝ)..time,
        Real.exp (rates index * (time - current)) * inputs index current) :
    ∀ time ∈ Icc 0 horizon,
      ‖fun index : Index => if index ∈ selected then states index time else 0‖ ≤
        multiplier * ∫ current in (0 : ℝ)..time,
          Real.exp (growth * (time - current)) * forcing current := by
  classical
  intro time inside
  have subset : Icc (0 : ℝ) time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl inside.2
  have commonKernel : Continuous (fun current : ℝ => Real.exp (growth * (time - current))) := by
    fun_prop
  have commonIntegrable :=
    (commonKernel.continuousOn.mul (forcingContinuous.mono subset)).intervalIntegrable_of_Icc
      (μ := volume) inside.1
  have majorantNonnegative : 0 ≤ multiplier * ∫ current in (0 : ℝ)..time,
      Real.exp (growth * (time - current)) * forcing current :=
    mul_nonneg multiplierNonnegative (intervalIntegral.integral_nonneg inside.1 (fun current member =>
      mul_nonneg (Real.exp_pos _).le (forcingNonnegative current (subset member))))
  apply (pi_norm_le_iff_of_nonneg majorantNonnegative).mpr
  intro index
  by_cases member : index ∈ selected
  · simp only [member, ite_true, Real.norm_eq_abs, abs_of_nonneg (statesNonnegative index member time inside)]
    have individualKernel : Continuous (fun current : ℝ => Real.exp (rates index * (time - current))) := by
      fun_prop
    have individualIntegrable :=
      (individualKernel.continuousOn.mul ((inputsContinuous index member).mono subset)).intervalIntegrable_of_Icc
        (μ := volume) inside.1
    have comparison := intervalIntegral.integral_mono_on inside.1 individualIntegrable commonIntegrable (by
      intro current currentInside
      have fullInside := subset currentInside
      have kernelBound := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (ratesBound index member) (sub_nonneg.mpr currentInside.2))
      exact (mul_le_mul_of_nonneg_left (inputBound index member current fullInside) (Real.exp_pos _).le).trans
        (mul_le_mul_of_nonneg_right kernelBound (forcingNonnegative current fullInside)))
    exact (propagator index member time inside).trans
      (mul_le_mul_of_nonneg_left comparison multiplierNonnegative)
  · simp only [member, ite_false, norm_zero]
    exact majorantNonnegative

end EulerNonuniqueness.General
