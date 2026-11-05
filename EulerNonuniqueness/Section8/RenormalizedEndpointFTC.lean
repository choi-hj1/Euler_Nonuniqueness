import EulerNonuniqueness.Section8.RenormalizedMassRegularization
import EulerNonuniqueness.Section8.RenormalizedTemporal
import EulerNonuniqueness.Section8.TransportAnalyticPDE

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

theorem TransportAnalyticHypotheses.renormalized_mollification_endpoint_identity
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega) (positive : 0 < horizon)
    {renormalization : ℝ → ℝ} (smooth : ContDiff ℝ 1 renormalization)
    (index : ℕ) (position : Plane) {time : ℝ} (inside : time ∈ Icc 0 horizon) :
    (∫ other in Ioo 0 time, deriv renormalization (mollification (omega other) index position) *
      (transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega other)) (omega other) position -
        fderiv ℝ (mollification (omega other) index) position (biotSavart (omega other) position))) =
      renormalization (mollification (omega time) index position) -
        renormalization (mollification (omega 0) index position) := by
  have subset : Icc 0 time ⊆ Icc 0 horizon := Icc_subset_Icc le_rfl inside.2
  have valueContinuous : ContinuousOn (fun other => renormalization (mollification (omega other) index position))
      (Icc 0 horizon) := continuousOn_iff_continuous_restrict.mpr
        (smooth.continuous.comp (hypotheses.continuous_mollification_time index position))
  have sourceContinuous : ContinuousOn (fun other => deriv renormalization (mollification (omega other) index position) *
      (transportCommutator ((mollifierBump index).normed volume) (biotSavart (omega other)) (omega other) position -
        fderiv ℝ (mollification (omega other) index) position (biotSavart (omega other) position))) (Icc 0 horizon) := by
    apply continuousOn_iff_continuous_restrict.mpr
    exact (((smooth.continuous_deriv le_rfl).comp (hypotheses.continuous_mollification_time index position)).mul
      ((hypotheses.continuous_transportCommutator_time (mollifierBump index).contDiff_normed
        (mollifierBump index).hasCompactSupport_normed position).sub
          (hypotheses.continuous_mollifiedAdvectiveDerivative_time index position)))
  have identity := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le inside.1
    (valueContinuous.mono subset)
    (fun other otherInside => hypotheses.hasDerivAt_renormalized_mollification positive smooth index position
      ⟨otherInside.1, lt_of_lt_of_le otherInside.2 inside.2⟩)
    ((sourceContinuous.mono subset).intervalIntegrable_of_Icc inside.1)
  rw [intervalIntegral.integral_of_le inside.1, integral_Ioc_eq_integral_Ioo] at identity
  exact identity

end EulerNonuniqueness
