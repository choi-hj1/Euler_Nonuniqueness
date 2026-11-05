import EulerNonuniqueness.General.InteriorDerivativeError

noncomputable section

open Set Filter MeasureTheory

namespace EulerNonuniqueness.General

theorem norm_sub_le_integral_of_interior_derivative_majorant
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {curve derivative : ℝ → Space} {majorant : ℝ → ℝ} {terminal : ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (curveContinuous : ContinuousOn curve (Icc 0 terminal))
    (majorantContinuous : ContinuousOn majorant (Icc 0 terminal))
    (majorantNonnegative : ∀ time ∈ Icc 0 terminal, 0 ≤ majorant time)
    (equation : ∀ time ∈ Ioo 0 terminal, HasDerivAt curve (derivative time) time)
    (bounded : ∀ time ∈ Ioo 0 terminal, ‖derivative time‖ ≤ majorant time) :
    ‖curve terminal - curve 0‖ ≤ ∫ time in (0 : ℝ)..terminal, majorant time := by
  let actual := (Ioo (0 : ℝ) terminal).indicator (deriv curve)
  have actualBound (time : ℝ) (inside : time ∈ Icc 0 terminal) : ‖actual time‖ ≤ majorant time := by
    by_cases interior : time ∈ Ioo 0 terminal
    · simpa only [actual, indicator_of_mem interior, (equation time interior).deriv] using bounded time interior
    · simpa only [actual, indicator_of_not_mem interior, norm_zero] using majorantNonnegative time inside
  have measurable : AEStronglyMeasurable actual (volume.restrict (Icc 0 terminal)) :=
    ((stronglyMeasurable_deriv curve).indicator measurableSet_Ioo).aestronglyMeasurable
  have majorantIntegrable := majorantContinuous.integrableOn_Icc (μ := volume)
  have actualIntegrable : IntegrableOn actual (Icc 0 terminal) := majorantIntegrable.mono' measurable
    ((ae_restrict_mem measurableSet_Icc).mono (fun time inside => actualBound time inside))
  have interior (time : ℝ) (inside : time ∈ Ioo 0 terminal) : HasDerivAt curve (actual time) time := by
    simpa only [actual, indicator_of_mem inside, (equation time inside).deriv] using equation time inside
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le terminalNonnegative curveContinuous interior
    ((intervalIntegrable_iff_integrableOn_Icc_of_le terminalNonnegative).mpr actualIntegrable)
  rw [← fundamental]
  apply (intervalIntegral.norm_integral_le_integral_norm terminalNonnegative).trans
  exact intervalIntegral.integral_mono_on terminalNonnegative
    ((intervalIntegrable_iff_integrableOn_Icc_of_le terminalNonnegative).mpr actualIntegrable).norm
    (majorantContinuous.intervalIntegrable_of_Icc terminalNonnegative) actualBound

end EulerNonuniqueness.General
