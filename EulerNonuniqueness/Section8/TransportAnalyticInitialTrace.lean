import EulerNonuniqueness.Section8.TransportAnalyticPDE
import EulerNonuniqueness.Section8.SeparableInitialTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.initial_smooth_moment
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) {test : Plane → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ position, omega 0 position * test position) = ∫ position, initial position * test position := by
  let temporal : ContDiffBump (0 : ℝ) := ⟨horizon / 4, horizon / 2, by positivity, by linarith⟩
  have temporalAtZero : temporal 0 = 1 := temporal.one_of_mem_closedBall (by simp [temporal]; positivity)
  have temporalZero (time : ℝ) (after : horizon ≤ time) : temporal time = 0 := by
    apply temporal.zero_of_le_dist
    have nonnegative : 0 ≤ time := horizonPositive.le.trans after
    simp only [Real.dist_eq, sub_zero, abs_of_nonneg nonnegative]
    change horizon / 2 ≤ time
    linarith
  let moment := fun time => ∫ position, omega time position * test position
  let flux := fun time => ∫ position, omega time position * fderiv ℝ test position (biotSavart (omega time) position)
  have momentContinuous : ContinuousOn moment (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (hypotheses.weakL2Continuous.2 test (smooth.continuous.memLp_of_hasCompactSupport compact))
  have fluxContinuous : ContinuousOn flux (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr (hypotheses.continuous_transportFlux smooth compact)
  have productFTC := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le horizonPositive.le] using momentContinuous)
    temporal.continuous.continuousOn
    (fun point inside => hypotheses.hasDerivAt_smooth_moment horizonPositive smooth compact
      (by simpa only [min_eq_left horizonPositive.le, max_eq_right horizonPositive.le] using inside))
    (fun point _ => ((show ContDiff ℝ 1 temporal from temporal.contDiff).differentiable le_rfl point).hasDerivAt)
    (fluxContinuous.intervalIntegrable_of_Icc horizonPositive.le)
    (((show ContDiff ℝ 1 temporal from temporal.contDiff).continuous_deriv le_rfl).intervalIntegrable 0 horizon)
  have weakIdentity := hypotheses.weakTransport.separableTest_initial_identity temporal.contDiff
    temporal.hasCompactSupport temporalZero smooth compact
    (fun _ inside => hypotheses.integrable_smooth_moment inside smooth compact)
    (fun _ inside => hypotheses.integrable_transportFlux inside smooth compact)
  rw [temporalZero horizon le_rfl, temporalAtZero, mul_zero, mul_one, zero_sub] at productFTC
  rw [temporalAtZero, mul_one] at weakIdentity
  rw [intervalIntegral.integral_of_le horizonPositive.le, integral_Ioc_eq_integral_Ioo] at productFTC
  have productEquality : (∫ time in Ioo 0 horizon, moment time * deriv temporal time + flux time * temporal time) =
      -moment 0 := by
    convert productFTC using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun _ => add_comm _ _
  change (∫ time in Ioo 0 horizon, moment time * deriv temporal time + flux time * temporal time) + _ = 0 at weakIdentity
  rw [productEquality] at weakIdentity
  linarith

theorem TransportAnalyticHypotheses.mollification_initial_trace
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    (horizonPositive : 0 < horizon) (index : ℕ) (position : Plane) :
    mollification (omega 0) index position = mollification initial index position := by
  rw [mollification_eq_source_moment, mollification_eq_source_moment]
  exact hypotheses.initial_smooth_moment horizonPositive
    ((mollifierBump index).contDiff_normed.comp (contDiff_const.sub contDiff_id))
    ((mollifierBump index).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft position))

theorem TransportAnalyticHypotheses.continuous_mollification_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon => mollification (omega time) index position) := by
  have smooth : ContDiff ℝ ∞ (fun source => (mollifierBump index).normed volume (position - source)) :=
    (mollifierBump index).contDiff_normed.comp (contDiff_const.sub contDiff_id)
  have compact : HasCompactSupport (fun source => (mollifierBump index).normed volume (position - source)) :=
    (mollifierBump index).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft position)
  convert hypotheses.weakL2Continuous.2 _ (smooth.continuous.memLp_of_hasCompactSupport compact) using 1
  funext time
  exact mollification_eq_source_moment (omega time) index position

end EulerNonuniqueness
