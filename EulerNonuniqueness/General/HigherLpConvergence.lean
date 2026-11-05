import EulerNonuniqueness.General.UniformLpIntegrability

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

theorem tendsto_eLpNorm_of_tendsto_eLpNorm_of_uniform_higherLp
    {Domain Value : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} [IsFiniteMeasure measure]
    {sequence : ℕ → Domain → Value} {limit : Domain → Value}
    {exponent topologyExponent higherExponent : ℝ≥0∞}
    (exponentBound : 1 ≤ exponent) (higherStrict : exponent < higherExponent)
    (higherFinite : higherExponent ≠ ∞) (topologyNonzero : topologyExponent ≠ 0)
    (measurable : ∀ index, AEStronglyMeasurable (sequence index) measure)
    (limitMember : MemLp limit exponent measure) {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ index, eLpNorm (sequence index) higherExponent measure ≤ ENNReal.ofReal bound)
    (converges : Tendsto (fun index => eLpNorm (sequence index - limit) topologyExponent measure)
      atTop (𝓝 0)) :
    Tendsto (fun index => eLpNorm (sequence index - limit) exponent measure) atTop (𝓝 0) := by
  have exponentPositive : 0 < exponent := zero_lt_one.trans_le exponentBound
  have uniformlyIntegrable := EulerNonuniqueness.unifIntegrable_of_uniform_higherLp
    exponentPositive higherStrict higherFinite measurable boundNonnegative bounded
  have inMeasure := tendstoInMeasure_of_tendsto_eLpNorm topologyNonzero measurable
    limitMember.aestronglyMeasurable converges
  exact tendsto_Lp_finite_of_tendstoInMeasure exponentBound (higherStrict.trans_le le_top).ne
    measurable limitMember uniformlyIntegrable inMeasure

theorem eventually_uniform_eLpNorm_lt_of_uniform_other_eLpNorm_lt
    {Domain Value Parameter : Type*} [MeasurableSpace Domain] [NormedAddCommGroup Value]
    {measure : Measure Domain} [IsFiniteMeasure measure]
    {fields : ℕ → Parameter → Domain → Value} {exponent topologyExponent higherExponent : ℝ≥0∞}
    (exponentBound : 1 ≤ exponent) (higherStrict : exponent < higherExponent)
    (higherFinite : higherExponent ≠ ∞) (topologyNonzero : topologyExponent ≠ 0)
    (measurable : ∀ index parameter, AEStronglyMeasurable (fields index parameter) measure)
    {bound : ℝ} (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ index parameter, eLpNorm (fields index parameter) higherExponent measure ≤ ENNReal.ofReal bound)
    (converges : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop, ∀ parameter,
      eLpNorm (fields index parameter) topologyExponent measure < ENNReal.ofReal tolerance)
    {tolerance : ℝ} (positive : 0 < tolerance) :
    ∀ᶠ index in atTop, ∀ parameter,
      eLpNorm (fields index parameter) exponent measure < ENNReal.ofReal tolerance := by
  by_contra failure
  have frequent := not_eventually.mp failure
  have choices (step : ℕ) : ∃ index : ℕ, step ≤ index ∧ ∃ parameter : Parameter,
      ENNReal.ofReal tolerance ≤ eLpNorm (fields index parameter) exponent measure := by
    obtain ⟨index, lower, bad⟩ := frequently_atTop.mp frequent step
    push_neg at bad
    obtain ⟨parameter, large⟩ := bad
    exact ⟨index, lower, parameter, large⟩
  choose indices lower parameters large using choices
  have indicesTend := tendsto_atTop_mono lower tendsto_id
  have otherConverges : Tendsto
      (fun step => eLpNorm (fields (indices step) (parameters step)) topologyExponent measure) atTop (𝓝 0) := by
    apply ENNReal.tendsto_nhds_zero.mpr
    intro epsilon epsilonPositive
    by_cases finite : epsilon = ∞
    · simp only [finite, le_top, eventually_true]
    · have small := indicesTend.eventually (converges epsilon.toReal
        (ENNReal.toReal_pos epsilonPositive.ne' finite))
      filter_upwards [small] with step bound
      simpa only [ENNReal.ofReal_toReal finite] using (bound (parameters step)).le
  have upgraded := tendsto_eLpNorm_of_tendsto_eLpNorm_of_uniform_higherLp
    (sequence := fun step => fields (indices step) (parameters step)) (limit := 0)
    exponentBound higherStrict higherFinite topologyNonzero
    (fun step => measurable (indices step) (parameters step)) (MemLp.zero : MemLp (0 : Domain → Value) exponent measure)
    boundNonnegative (fun step => bounded (indices step) (parameters step))
    (by simpa only [sub_zero] using otherConverges)
  have small := upgraded.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr positive))
  obtain ⟨step, small⟩ := small.exists
  exact (not_lt_of_ge (large step)) (by simpa only [sub_zero] using small)

end MeasureTheory
