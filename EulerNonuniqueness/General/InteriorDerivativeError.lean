import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem norm_sub_le_of_continuousOn_interior_derivative_bound
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {function derivative : ℝ → Space} {terminal bound : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (boundNonnegative : 0 ≤ bound)
    (continuous : ContinuousOn function (Icc 0 terminal))
    (equation : ∀ time ∈ Ioo 0 terminal, HasDerivAt function (derivative time) time)
    (bounded : ∀ time ∈ Ioo 0 terminal, ‖derivative time‖ ≤ bound) :
    ‖function terminal - function 0‖ ≤ bound * terminal := by
  let actual := (Ioo (0 : ℝ) terminal).indicator (deriv function)
  have actualBound (time : ℝ) : ‖actual time‖ ≤ bound := by
    by_cases inside : time ∈ Ioo 0 terminal
    · simpa only [actual, indicator_of_mem inside, (equation time inside).deriv] using bounded time inside
    · simpa only [actual, indicator_of_not_mem inside, norm_zero] using boundNonnegative
  have measurable : AEStronglyMeasurable actual (volume.restrict (Icc 0 terminal)) :=
    ((stronglyMeasurable_deriv function).indicator measurableSet_Ioo).aestronglyMeasurable
  have integrable : IntegrableOn actual (Icc 0 terminal) :=
    (integrableOn_const.mpr (Or.inr isCompact_Icc.measure_lt_top)).mono' measurable
      (Filter.Eventually.of_forall actualBound)
  have interior (time : ℝ) (inside : time ∈ Ioo 0 terminal) : HasDerivAt function (actual time) time := by
    simpa only [actual, indicator_of_mem inside, (equation time inside).deriv] using equation time inside
  have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le terminalNonnegative continuous interior
    ((intervalIntegrable_iff_integrableOn_Icc_of_le terminalNonnegative).mpr integrable)
  have estimate := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun time (_ : time ∈ uIoc 0 terminal) => actualBound time)
  rw [fundamental, sub_zero, abs_of_nonneg terminalNonnegative] at estimate
  exact estimate

theorem norm_sub_integral_le_of_interior_derivative_error
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {function derivative source : ℝ → Space} {terminal error : ℝ}
    (terminalNonnegative : 0 ≤ terminal) (errorNonnegative : 0 ≤ error)
    (functionContinuous : ContinuousOn function (Icc 0 terminal))
    (equation : ∀ time ∈ Ioo 0 terminal, HasDerivAt function (derivative time) time)
    (sourceContinuous : ContinuousOn source (Icc 0 terminal))
    (bound : ∀ time ∈ Ioo 0 terminal, ‖derivative time - source time‖ ≤ error) :
    ‖function terminal - function 0 - ∫ time in (0 : ℝ)..terminal, source time‖ ≤ error * terminal := by
  let extension : ℝ → Space := fun time => source (projIcc 0 terminal terminalNonnegative time)
  have extensionContinuous : Continuous extension :=
    (continuousOn_iff_continuous_restrict.mp sourceContinuous).comp continuous_projIcc
  have agreement : EqOn extension source (Icc 0 terminal) := by
    intro time member
    simp only [extension, projIcc_of_mem terminalNonnegative member]
  let primitive : ℝ → Space := fun time => ∫ current in (0 : ℝ)..time, extension current
  have primitiveEquation (time : ℝ) : HasDerivAt primitive (extension time) time :=
    intervalIntegral.integral_hasDerivAt_right (extensionContinuous.intervalIntegrable 0 time)
      extensionContinuous.aestronglyMeasurable.stronglyMeasurableAtFilter extensionContinuous.continuousAt
  have residualEquation (time : ℝ) (member : time ∈ Ioo 0 terminal) :
      HasDerivAt (fun current => function current - primitive current)
        (derivative time - source time) time := by
    have actual := (equation time member).sub (primitiveEquation time)
    rw [agreement ⟨member.1.le, member.2.le⟩] at actual
    exact actual
  have primitiveContinuous : Continuous primitive :=
    continuous_iff_continuousAt.mpr fun time => (primitiveEquation time).continuousAt
  have estimate := norm_sub_le_of_continuousOn_interior_derivative_bound terminalNonnegative errorNonnegative
    (functionContinuous.sub primitiveContinuous.continuousOn) residualEquation bound
  have integralIdentity : primitive terminal = ∫ time in (0 : ℝ)..terminal, source time := by
    apply intervalIntegral.integral_congr
    intro time member
    exact agreement (by simpa only [uIcc_of_le terminalNonnegative] using member)
  have primitiveZero : primitive 0 = 0 := intervalIntegral.integral_same
  rw [primitiveZero, sub_zero, integralIdentity] at estimate
  convert estimate using 1
  congr 1
  abel

end EulerNonuniqueness
