import EulerNonuniqueness.General.L2PairingContinuity

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace MeasureTheory

theorem MemLp.apply_bounded_continuousLinearMap
    {Domain Source Value : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} {field : Domain → Source}
    {operators : Domain → Source →L[ℝ] Value} {bound : ℝ}
    (member : MemLp field exponent measure)
    (measurable : AEStronglyMeasurable operators measure)
    (bounded : ∀ point, ‖operators point‖ ≤ bound) :
    MemLp (fun point => operators point (field point)) exponent measure := by
  exact member.of_le_mul
    ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (measurable.prodMk member.aestronglyMeasurable))
    (Filter.Eventually.of_forall fun point =>
      ((operators point).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (bounded point) (norm_nonneg _)))

theorem tendsto_eLpNorm_apply_bounded_continuousLinearMap_sub
    {Domain Source Value Index : Type*} [MeasurableSpace Domain]
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent : ℝ≥0∞} {filter : Filter Index}
    {sequence : Index → Domain → Source} {limit : Domain → Source}
    {operators : Domain → Source →L[ℝ] Value} {bound : ℝ}
    (bounded : ∀ point, ‖operators point‖ ≤ bound)
    (converges : Tendsto (fun index => eLpNorm (sequence index - limit) exponent measure)
      filter (𝓝 0)) :
    Tendsto (fun index => eLpNorm
      ((fun point => operators point (sequence index point)) -
        (fun point => operators point (limit point))) exponent measure) filter (𝓝 0) := by
  have estimate (index : Index) : eLpNorm
      ((fun point => operators point (sequence index point)) -
        (fun point => operators point (limit point))) exponent measure ≤
      ENNReal.ofReal bound * eLpNorm (sequence index - limit) exponent measure := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
    exact Filter.Eventually.of_forall fun point => by
      change ‖operators point (sequence index point) - operators point (limit point)‖ ≤ _
      rw [← map_sub]
      exact ((operators point).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (bounded point) (norm_nonneg _))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun index => ENNReal.ofReal bound *
      eLpNorm (sequence index - limit) exponent measure) filter (𝓝 0) by
        simpa only [mul_zero] using
          ENNReal.Tendsto.const_mul converges (Or.inr ENNReal.ofReal_ne_top))
    (fun _ => zero_le _) estimate

end MeasureTheory
