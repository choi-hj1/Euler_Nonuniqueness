import EulerNonuniqueness.Section8.TransportAnalyticFlux
import EulerNonuniqueness.Section8.SeparableTransport
import EulerNonuniqueness.General.IntervalWeakDerivative
import EulerNonuniqueness.General.DerivativeFromIntervalFTC

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.smooth_moment_sub_eq_intervalIntegral
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {first second : ℝ} (firstInside : first ∈ Icc 0 horizon) (secondInside : second ∈ Icc 0 horizon) :
    (∫ position, omega second position * test position) -
      (∫ position, omega first position * test position) =
      ∫ time in first..second, ∫ position, omega time position * fderiv ℝ test position (biotSavart (omega time) position) := by
  have momentContinuous : ContinuousOn (fun time => ∫ position, omega time position * test position) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (hypotheses.weakL2Continuous.2 test (smooth.continuous.memLp_of_hasCompactSupport compact))
  have fluxContinuous : ContinuousOn (fun time => ∫ position, omega time position *
      fderiv ℝ test position (biotSavart (omega time) position)) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr (hypotheses.continuous_transportFlux smooth compact)
  refine momentContinuous.sub_eq_intervalIntegral_of_weak_derivative_setIntegral
    fluxContinuous horizonPositive ?_ firstInside secondInside
  intro temporal temporalSmooth temporalCompact temporalSupport
  exact (hypotheses.weakTransport.separableTest_identity temporalSmooth temporalCompact temporalSupport
    smooth compact (fun _ inside => hypotheses.integrable_smooth_moment inside smooth compact)
    (fun _ inside => hypotheses.integrable_transportFlux inside smooth compact)).2

theorem TransportAnalyticHypotheses.hasDerivAt_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    {time : ℝ} (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun other => ∫ source, omega other source * test source)
      (∫ source, omega time source * fderiv ℝ test source (biotSavart (omega time) source)) time := by
  have sourceContinuous : ContinuousOn (fun other => ∫ source, omega other source *
      fderiv ℝ test source (biotSavart (omega other) source)) (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr (hypotheses.continuous_transportFlux smooth compact)
  exact hasDerivAt_of_sub_eq_intervalIntegral_on_Icc
    (function := fun other => ∫ source, omega other source * test source)
    sourceContinuous horizonPositive
    (fun other otherInside => hypotheses.smooth_moment_sub_eq_intervalIntegral horizonPositive
      smooth compact (first := 0) (second := other) ⟨le_rfl, horizonPositive.le⟩ otherInside) inside

end EulerNonuniqueness
