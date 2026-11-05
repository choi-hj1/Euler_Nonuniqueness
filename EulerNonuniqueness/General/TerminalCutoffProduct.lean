import EulerNonuniqueness.General.TerminalCutoff

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness

theorem integrable_terminalCutoff_smul {Domain Value : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure (ℝ × Domain)} {field : ℝ × Domain → Value} (integrable : Integrable field measure)
    (horizon : ℝ) (index : ℕ) :
    Integrable (fun point => terminalCutoff horizon index point.1 • field point) measure := by
  apply integrable.norm.mono'
    (((contDiff_terminalCutoff horizon index).continuous.measurable.comp measurable_fst).aestronglyMeasurable.smul
      integrable.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun point => by
    rw [norm_smul, Real.norm_eq_abs, Function.comp_apply, abs_of_nonneg (terminalCutoff_bounds horizon index point.1).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (terminalCutoff_bounds horizon index point.1).2

theorem tendsto_integral_terminalCutoff_smul {Domain Value : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] {measure : Measure Domain} [SFinite measure]
    {horizon : ℝ} (positive : 0 < horizon) {field : ℝ × Domain → Value}
    (integrable : Integrable field ((volume.restrict (Ioo 0 horizon)).prod measure)) :
    Tendsto (fun index => ∫ point, terminalCutoff horizon index point.1 • field point
      ∂((volume.restrict (Ioo 0 horizon)).prod measure)) atTop
        (𝓝 (∫ point, field point ∂((volume.restrict (Ioo 0 horizon)).prod measure))) := by
  apply tendsto_integral_of_dominated_convergence (fun point => ‖field point‖)
  · exact fun index => (integrable_terminalCutoff_smul integrable horizon index).aestronglyMeasurable
  · exact integrable.norm
  · intro index
    exact Filter.Eventually.of_forall fun point => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (terminalCutoff_bounds horizon index point.1).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (terminalCutoff_bounds horizon index point.1).2
  · have timeInside : ∀ᵐ point ∂((volume.restrict (Ioo 0 horizon)).prod measure), point.1 ∈ Ioo 0 horizon :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioo)
    filter_upwards [timeInside] with point inside
    apply tendsto_const_nhds.congr'
    exact (terminalCutoff_eventually_one positive inside.2).mono fun index equal => by simp only [equal, one_smul]

end EulerNonuniqueness
