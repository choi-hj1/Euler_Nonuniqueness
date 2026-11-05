import EulerNonuniqueness.Section8.WeakLimitSpacetimeTransport
import EulerNonuniqueness.Section8.WeakLimitPathConstruction

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem WeakVorticityLimitPath.transportAnalyticHypotheses
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution} {subsequence : ℕ → ℕ}
    {limit : Evolution} (path : WeakVorticityLimitPath horizon sequence subsequence limit)
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (nonnegative : 0 ≤ horizon)
    (increasing : StrictMono subsequence) : TransportAnalyticHypotheses horizon initial limit := by
  refine ⟨path.weakTransportOn hypotheses nonnegative increasing, path.weakL2Continuous,
    path.supported, ?_, path.uniformBounds, ?_⟩
  · intro exponent bound time inside
    exact path.membership exponent bound inside
  · intro time inside
    exact (path.datum time inside).2.2

theorem LocalCompactnessHypotheses.exists_transport_analytic_limit
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence) (positive : 0 < horizon) :
    ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∃ limit : Evolution,
      WeakVorticityLimitPath horizon sequence subsequence limit ∧
        TransportAnalyticHypotheses horizon initial limit := by
  obtain ⟨subsequence, increasing, limit, path⟩ := hypotheses.exists_weak_vorticity_limit_path positive
  exact ⟨subsequence, increasing, limit, path,
    path.transportAnalyticHypotheses hypotheses positive.le increasing⟩

end EulerNonuniqueness
