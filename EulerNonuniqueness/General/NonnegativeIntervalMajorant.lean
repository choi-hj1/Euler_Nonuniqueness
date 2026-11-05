import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.General

theorem intervalIntegral_le_of_nonnegative_majorant
    {first second : ℝ → ℝ} {terminal : ℝ} (terminalNonnegative : 0 ≤ terminal)
    (firstNonnegative : ∀ time ∈ Icc 0 terminal, 0 ≤ first time)
    (secondContinuous : ContinuousOn second (Icc 0 terminal))
    (bound : ∀ time ∈ Icc 0 terminal, first time ≤ second time) :
    (∫ time in (0 : ℝ)..terminal, first time) ≤ ∫ time in (0 : ℝ)..terminal, second time := by
  rw [intervalIntegral.integral_of_le terminalNonnegative, intervalIntegral.integral_of_le terminalNonnegative]
  have inside : ∀ᵐ time : ℝ ∂(volume.restrict (Ioc (0 : ℝ) terminal)), time ∈ Ioc (0 : ℝ) terminal :=
    ae_restrict_mem measurableSet_Ioc
  exact MeasureTheory.integral_mono_of_nonneg
    (inside.mono fun time member => firstNonnegative time ⟨member.1.le, member.2⟩)
    (secondContinuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (inside.mono fun time member => bound time ⟨member.1.le, member.2⟩)

end EulerNonuniqueness.General
