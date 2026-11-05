import EulerNonuniqueness.Section8.ExpandingEulerSequence
import EulerNonuniqueness.Section8.TransportAnalyticHypotheses

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace EulerNonuniqueness

theorem ContinuousInLp.on_interval {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [MeasurableSpace Value] [BorelSpace Value]
    {exponent : ℝ≥0∞} {field : ℝ → Plane → Value}
    (continuity : ContinuousInLp exponent field) (horizon : ℝ) :
    ContinuousInLpOn horizon exponent field := by
  obtain ⟨bound, membership, continuous⟩ := continuity
  letI : Fact (1 ≤ exponent) := ⟨bound⟩
  let inclusion : Icc (0 : ℝ) horizon → ℝ≥0 := fun time => ⟨time, time.property.1⟩
  have inclusionContinuous : Continuous inclusion := continuous_subtype_val.subtype_mk _
  exact ⟨bound, fun time => membership (inclusion time), continuous.comp inclusionContinuous⟩

theorem IsEulerSolution.on_interval {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolution initial omega) {horizon : ℝ} (positive : 0 < horizon) :
    IsEulerSolutionOn horizon initial omega := by
  rcases solution with ⟨initialEqual, continuous, velocityContinuous, integrable,
    conserved, divergence, transport, renormalized, momentum⟩
  exact ⟨initialEqual, fun exponent bound => (continuous exponent bound).on_interval horizon,
    velocityContinuous.on_interval horizon, fun time inside => integrable time inside.1,
    fun exponent bound time inside => conserved exponent bound time inside.1,
    fun time inside => divergence time inside.1, transport horizon positive,
    fun renormalization admissible => renormalized renormalization admissible horizon positive,
    momentum horizon positive⟩

theorem IsEulerSolutionOn.transportAnalyticHypotheses
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (solution : IsEulerSolutionOn horizon initial omega) (datum : InitialDatum initial)
    (supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
      Function.support (omega time) ⊆ Metric.closedBall 0 radius)
    (zeroMean : ∀ time ∈ Icc 0 horizon, (∫ position, omega time position) = 0) :
    TransportAnalyticHypotheses horizon initial omega := by
  refine ⟨solution.2.2.2.2.2.2.1, solution.weakL2ContinuousOn, supported,
    fun _ exponentBound _ inside => solution.memLp exponentBound inside, ?_, zeroMean⟩
  intro exponent exponentBound
  refine ⟨eLpNorm initial (ENNReal.ofReal exponent) volume,
    (datum.2.1 exponent exponentBound).eLpNorm_lt_top, ?_⟩
  intro time inside
  exact (solution.2.2.2.2.1 exponent exponentBound time inside).le

end EulerNonuniqueness
