import EulerNonuniqueness.Section8.TransportAnalyticInitialTrace
import EulerNonuniqueness.Section8.TransportAnalyticCommutator
import EulerNonuniqueness.Section8.TestSlices
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.continuous_mollifiedAdvectiveDerivative_time
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (index : ℕ) (position : Plane) :
    Continuous (fun time : Icc (0 : ℝ) horizon => fderiv ℝ (mollification (omega time) index) position
      (biotSavart (omega time) position)) := by
  have velocityContinuous := hypotheses.continuous_biotSavart_time position
  have smooth : ContDiff ℝ ∞ ((mollifierBump index).normed (volume : Measure Plane)) :=
    (mollifierBump index).contDiff_normed
  have compact : HasCompactSupport ((mollifierBump index).normed (volume : Measure Plane)) :=
    (mollifierBump index).hasCompactSupport_normed
  have result := (((Complex.continuous_re.comp velocityContinuous).mul
      (hypotheses.continuous_mollifiedDerivative_time smooth compact position 1)).add
      ((Complex.continuous_im.comp velocityContinuous).mul
        (hypotheses.continuous_mollifiedDerivative_time smooth compact position Complex.I)))
  convert result using 1
  funext time
  rw [realLinearMap_apply_complex]
  simp only [Function.comp_apply, mollification]

theorem TransportAnalyticHypotheses.renormalized_temporal_test_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (horizonPositive : 0 < horizon)
    {renormalization : ℝ → ℝ} (renormalizationSmooth : ContDiff ℝ 1 renormalization)
    {test : ℝ × Plane → ℝ} (testAdmissible : ScalarTestOn horizon test)
    (index : ℕ) (position : Plane) :
    (∫ time in Ioo 0 horizon,
      renormalization (mollification (omega time) index position) * timeDerivative test (time, position) +
      deriv renormalization (mollification (omega time) index position) *
        (transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega time)) (omega time) position -
          fderiv ℝ (mollification (omega time) index) position (biotSavart (omega time) position)) * test (time, position)) +
      renormalization (mollification initial index position) * test (0, position) = 0 := by
  let regularized := fun time => renormalization (mollification (omega time) index position)
  let source := fun time => deriv renormalization (mollification (omega time) index position) *
    (transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega time)) (omega time) position -
      fderiv ℝ (mollification (omega time) index) position (biotSavart (omega time) position))
  have regularizedContinuous : ContinuousOn regularized (Icc 0 horizon) :=
    continuousOn_iff_continuous_restrict.mpr
      (renormalizationSmooth.continuous.comp (hypotheses.continuous_mollification_time index position))
  have sourceContinuous : ContinuousOn source (Icc 0 horizon) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact (((renormalizationSmooth.continuous_deriv le_rfl).comp
      (hypotheses.continuous_mollification_time index position)).mul
        ((hypotheses.continuous_transportCommutator_time (mollifierBump index).contDiff_normed
          (mollifierBump index).hasCompactSupport_normed position).sub
            (hypotheses.continuous_mollifiedAdvectiveDerivative_time index position)))
  have temporalSmooth := contDiff_temporal_slice testAdmissible.1 position
  have productFTC := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le horizonPositive.le] using regularizedContinuous)
    temporalSmooth.continuous.continuousOn
    (fun point inside => hypotheses.hasDerivAt_renormalized_mollification horizonPositive
      renormalizationSmooth index position
      (by simpa only [min_eq_left horizonPositive.le, max_eq_right horizonPositive.le] using inside))
    (fun point _ => hasDerivAt_temporal_slice testAdmissible.1 point position)
    (sourceContinuous.intervalIntegrable_of_Icc horizonPositive.le)
    (((temporalSmooth.continuous_deriv (by simp)).intervalIntegrable 0 horizon).congr
      (Filter.Eventually.of_forall fun time => deriv_temporal_slice testAdmissible.1 time position))
  rw [testAdmissible.2.2 horizon position le_rfl, mul_zero, zero_sub] at productFTC
  rw [intervalIntegral.integral_of_le horizonPositive.le, integral_Ioc_eq_integral_Ioo] at productFTC
  have reordered : (∫ time in Ioo 0 horizon, regularized time * timeDerivative test (time, position) +
      source time * test (time, position)) = -regularized 0 * test (0, position) := by
    convert productFTC using 1
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => add_comm _ _
    · ring
  dsimp only [regularized, source] at reordered
  rw [hypotheses.mollification_initial_trace horizonPositive] at reordered
  linarith

end EulerNonuniqueness
