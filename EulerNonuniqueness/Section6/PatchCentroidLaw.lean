import EulerNonuniqueness.Section3.FiniteLiteralPatchCentroid
import EulerNonuniqueness.Section6.PatchSelfInteraction
import EulerNonuniqueness.Section8.UniformVelocityBounds

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_identity_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) : IntegrableOn (fun position : ℂ => position) (flow.domain time index) := by
  exact (continuous_id.continuousOn.integrableOn_compact
    (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure

theorem centroid_eq_complex_integral (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) :
    flow.centroid time index = (Real.pi * configuration.radius index ^ 2)⁻¹ •
      (∫ position in flow.domain time index, position) := by
  unfold centroid
  congr 1
  simpa only [integral_ofReal] using
    integral_coe_re_add_coe_im (flow.domain_identity_integrable time index)

theorem domain_velocity_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) :
    IntegrableOn (biotSavart (flow.vorticity time)) (flow.domain time index) := by
  let bound := (eLpNorm (flow.vorticity time) (ENNReal.ofReal (4 : ℝ)) volume).toReal *
      (eLpNorm ((Metric.ball (0 : ℂ) 1).indicator biotSavartKernel)
        (ENNReal.ofReal (4 / 3 : ℝ)) volume).toReal +
      (∫ source, ‖flow.vorticity time source‖) * (1 / (2 * Real.pi))
  have constantIntegrable : IntegrableOn (fun _ : ℂ => bound) (flow.domain time index) :=
    integrableOn_const.mpr (Or.inr (flow.domain_isBounded time index).measure_lt_top)
  apply constantIntegrable.mono'
    ((aestronglyMeasurable_biotSavart (flow.vorticity_integrable time).aestronglyMeasurable).restrict)
  exact Filter.Eventually.of_forall fun position => norm_biotSavart_le_L1_L4
    (flow.vorticity_integrable time) (flow.vorticity_memLp time _) position

theorem centroid_hasDerivAt_complex_integral (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    HasDerivAt (fun parameter => flow.centroid parameter index)
      ((Real.pi * configuration.radius index ^ 2)⁻¹ •
        (∫ position in flow.domain time index, biotSavart (flow.vorticity time) position)) time := by
  have identity :
      ((∫ position in flow.domain time index, (biotSavart (flow.vorticity time) position).re : ℝ) : ℂ) +
        ((∫ position in flow.domain time index, (biotSavart (flow.vorticity time) position).im : ℝ) : ℂ) * Complex.I =
      ∫ position in flow.domain time index, biotSavart (flow.vorticity time) position := by
    simpa only [integral_ofReal] using
      integral_coe_re_add_coe_im (flow.domain_velocity_integrable time index)
  simpa only [identity] using flow.centroid_hasDerivAt inside index

theorem domain_centroid_centered_integral (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) :
    (∫ position in flow.domain time index, position - flow.centroid time index) = 0 := by
  have constantIntegrable : IntegrableOn (fun _ : ℂ => flow.centroid time index)
      (flow.domain time index) :=
    integrableOn_const.mpr (Or.inr (flow.domain_isBounded time index).measure_lt_top)
  rw [integral_sub (f := fun position : ℂ => position)
    (g := fun _ : ℂ => flow.centroid time index)
    (flow.domain_identity_integrable time index) constantIntegrable, integral_const]
  have area : (volume.restrict (flow.domain time index)).real univ =
      Real.pi * configuration.radius index ^ 2 := by
    simpa only [Measure.real, Measure.restrict_apply_univ] using flow.domain_area inside index
  rw [area, flow.centroid_eq_complex_integral, smul_smul]
  have nonzero : Real.pi * configuration.radius index ^ 2 ≠ 0 :=
    mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 (ne_of_gt (configuration.radius_pos index)))
  rw [mul_inv_cancel₀ nonzero, one_smul, sub_self]

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
