import EulerNonuniqueness.Section3.FiniteLiteralPatchTransportIntegrability

open Set MeasureTheory
open scoped ContDiff

namespace EulerNonuniqueness.Paper

noncomputable section

namespace FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_test_spatial_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) {test : ℝ × ℂ → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    IntegrableOn (fun position => spatialDerivative test (time, position)
      (biotSavart (flow.vorticity time) position)) (flow.domain time index) := by
  obtain ⟨bound, nonnegative, bounded⟩ := scalarTest_uniform_bounds smooth compact
  have finite : volume (flow.domain time index) < ⊤ := (flow.domain_isBounded time index).measure_lt_top
  have constant_integrable : IntegrableOn (fun _ : ℂ => bound * flow.speedBound) (flow.domain time index) :=
    integrableOn_const.mpr (Or.inr finite)
  have velocity_measurable := flow.measurable_biotSavart_joint.comp
    (measurable_const.prodMk measurable_id : Measurable (fun position : ℂ => (time, position)))
  have derivative_continuous := (smooth.continuous_fderiv (by simp)).comp
    (continuous_const.prodMk continuous_id : Continuous (fun position : ℂ => (time, position)))
  have measurable : AEStronglyMeasurable (fun position => spatialDerivative test (time, position)
      (biotSavart (flow.vorticity time) position)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (derivative_continuous.aestronglyMeasurable.prodMk
        (aestronglyMeasurable_const.prodMk velocity_measurable.aestronglyMeasurable))
  apply constant_integrable.mono' measurable.restrict
  exact Filter.Eventually.of_forall fun position =>
    ((bounded time position).2.2 _).trans
      (mul_le_mul_of_nonneg_left (flow.norm_biotSavart_le_speedBound time position) nonnegative)

theorem domain_test_temporal_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) {test : ℝ × ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) :
    IntegrableOn (fun position => timeDerivative test (time, position)) (flow.domain time index) := by
  have continuous : Continuous (fun position => timeDerivative test (time, position)) :=
    ((smooth.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  exact affinePatchDomain_integrable_of_continuous (configuration.center index) (configuration.radius_pos index)
    (flow.shape time index) ((flow.nearby time index).trans_le (min_le_left _ _)) _ continuous

theorem domain_test_integrable (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) {test : ℝ × ℂ → ℝ}
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    IntegrableOn (fun position => timeDerivative test (time, position) + spatialDerivative test (time, position)
      (biotSavart (flow.vorticity time) position)) (flow.domain time index) :=
  (flow.domain_test_temporal_integrable time index smooth).add
    (flow.domain_test_spatial_integrable time index smooth compact)

end FiniteLiteralPatchFlow

end

end EulerNonuniqueness.Paper
