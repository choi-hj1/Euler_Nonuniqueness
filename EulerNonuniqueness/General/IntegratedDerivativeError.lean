import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness

theorem norm_sub_integral_le_of_derivative_error
    {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]
    {function derivative source : ℝ → Space} {terminal error : ℝ}
    (terminalNonnegative : 0 ≤ terminal)
    (equation : ∀ time ∈ Icc 0 terminal, HasDerivAt function (derivative time) time)
    (sourceContinuous : ContinuousOn source (Icc 0 terminal))
    (bound : ∀ time ∈ Icc 0 terminal, ‖derivative time - source time‖ ≤ error) :
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
  have residualEquation (time : ℝ) (member : time ∈ Icc 0 terminal) :
      HasDerivWithinAt (fun current => function current - primitive current)
        (derivative time - source time) (Icc 0 terminal) time := by
    have actual := (equation time member).sub (primitiveEquation time)
    rw [agreement member] at actual
    exact actual.hasDerivWithinAt
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment' residualEquation
    (fun time member => bound time ⟨member.1, member.2.le⟩) terminal ⟨terminalNonnegative, le_rfl⟩
  have integralIdentity : primitive terminal = ∫ time in (0 : ℝ)..terminal, source time := by
    apply intervalIntegral.integral_congr
    intro time member
    exact agreement (by simpa only [uIcc_of_le terminalNonnegative] using member)
  have primitiveZero : primitive 0 = 0 := intervalIntegral.integral_same
  rw [primitiveZero, sub_zero, sub_zero, integralIdentity] at estimate
  have rearrange : function terminal - (∫ time in (0 : ℝ)..terminal, source time) - function 0 =
      function terminal - function 0 - ∫ time in (0 : ℝ)..terminal, source time := by abel
  rwa [rearrange] at estimate

end EulerNonuniqueness
