import EulerNonuniqueness.General.WeakLpConvergence

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem tendsto_toLp_of_eLpNorm_sub {Domain Value Index : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] {measure : Measure Domain}
    {exponent : ℝ≥0∞} [Fact (1 ≤ exponent)] {filter : Filter Index}
    {sequence : Index → Domain → Value} {limit : Domain → Value}
    (members : ∀ index, MemLp (sequence index) exponent measure)
    (limitMember : MemLp limit exponent measure)
    (converges : Tendsto (fun index => eLpNorm (sequence index - limit) exponent measure) filter (𝓝 0)) :
    Tendsto (fun index => (members index).toLp (sequence index)) filter
      (𝓝 (limitMember.toLp limit)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have realConverges := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp converges
  simpa only [← MemLp.toLp_sub, Lp.norm_toLp, ENNReal.toReal_zero] using realConverges

theorem tendsto_integral_smul_of_eLpNorm_sub {Domain Value Index : Type*}
    [MeasurableSpace Domain] [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {measure : Measure Domain} {exponent conjugate : ℝ}
    [Fact (1 ≤ ENNReal.ofReal conjugate)] {filter : Filter Index}
    {sequence : Index → Domain → Value} {limit : Domain → Value} {weight : Domain → ℝ}
    (conjugacy : exponent.HolderConjugate conjugate)
    (weightMember : MemLp weight (ENNReal.ofReal exponent) measure)
    (members : ∀ index, MemLp (sequence index) (ENNReal.ofReal conjugate) measure)
    (limitMember : MemLp limit (ENNReal.ofReal conjugate) measure)
    (converges : Tendsto
      (fun index => eLpNorm (sequence index - limit) (ENNReal.ofReal conjugate) measure) filter (𝓝 0)) :
    Tendsto (fun index => ∫ point, weight point • sequence index point ∂measure) filter
      (𝓝 (∫ point, weight point • limit point ∂measure)) := by
  have lpConverges := tendsto_toLp_of_eLpNorm_sub members limitMember converges
  have paired := ((integralSmulCLM (Value := Value) conjugacy weightMember).continuous.tendsto
    (limitMember.toLp limit)).comp lpConverges
  change Tendsto (fun index => integralSmulCLM conjugacy weightMember ((members index).toLp (sequence index)))
    filter (𝓝 (integralSmulCLM conjugacy weightMember (limitMember.toLp limit))) at paired
  simpa only [Function.comp_apply, integralSmulCLM_toLp conjugacy weightMember] using paired

end EulerNonuniqueness
