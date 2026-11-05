import EulerNonuniqueness.Section6.PatchCentroidLaw

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Section6

theorem integrableOn_biotSavart_of_L1_L4_finite {vorticity : Vorticity}
    (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    {domain : Set ℂ} (finite : volume domain < ⊤) :
    IntegrableOn (biotSavart vorticity) domain := by
  let bound := (eLpNorm vorticity (ENNReal.ofReal (4 : ℝ)) volume).toReal *
      (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (∫ source, ‖vorticity source‖) * (1 / (2 * Real.pi))
  have constantIntegrable : IntegrableOn (fun _ : ℂ => bound) domain :=
    integrableOn_const.mpr (Or.inr finite)
  apply constantIntegrable.mono'
    ((aestronglyMeasurable_biotSavart integrable.aestronglyMeasurable).restrict)
  exact Filter.Eventually.of_forall fun position => norm_biotSavart_le_L1_L4 integrable membership position

end EulerNonuniqueness.Section6

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem centroid_hasDerivAt_external_integral (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter index)
      ((Real.pi * configuration.radius index ^ 2)⁻¹ •
        (∫ position in flow.domain time index, biotSavart (flow.vorticity time) position -
          biotSavart ((flow.domain time index).indicator (fun _ => configuration.density index)) position)) time := by
  have measurable := (flow.domain_isOpen time index).measurableSet
  have finite : volume (flow.domain time index) < ⊤ :=
    (flow.domain_isBounded time index).measure_lt_top
  have membership : MemLp ((flow.domain time index).indicator (fun _ => configuration.density index))
      (ENNReal.ofReal (4 : ℝ)) volume :=
    memLp_indicator_const _ measurable _ (Or.inr finite.ne)
  have ownIntegrable : Integrable ((flow.domain time index).indicator (fun _ => configuration.density index)) :=
    (integrable_indicator_iff measurable).mpr (integrableOn_const.mpr (Or.inr finite))
  have ownVelocityIntegrable := Section6.integrableOn_biotSavart_of_L1_L4_finite
    ownIntegrable membership finite
  obtain ⟨radius, _, radiusBound⟩ := (flow.domain_isBounded time index).exists_pos_norm_le
  have ownZero := Section6.integral_patch_self_interaction_density measurable
    (show flow.domain time index ⊆ Metric.closedBall 0 radius from fun position member => by
      simpa using radiusBound position member) (configuration.density index)
  rw [integral_sub (f := biotSavart (flow.vorticity time))
    (g := biotSavart ((flow.domain time index).indicator (fun _ => configuration.density index)))
    (flow.domain_velocity_integrable time index) ownVelocityIntegrable, ownZero, sub_zero]
  exact flow.centroid_hasDerivAt_complex_integral inside index

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
