import EulerNonuniqueness.Section8.Compactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology ContDiff

namespace EulerNonuniqueness

structure TransportAnalyticHypotheses (horizon : ℝ) (initial : Vorticity) (omega : Evolution) : Prop where
  weakTransport : WeakTransportOn horizon initial omega (fun time => biotSavart (omega time))
  weakL2Continuous : WeakL2ContinuousOn horizon omega
  supported : ∃ radius : ℝ, 0 < radius ∧ ∀ time ∈ Icc 0 horizon,
    Function.support (omega time) ⊆ Metric.closedBall 0 radius
  membership : ∀ exponent : ℝ, 1 ≤ exponent → ∀ time ∈ Icc 0 horizon,
    MemLp (omega time) (ENNReal.ofReal exponent) volume
  uniformBounds : ∀ exponent : ℝ, 1 ≤ exponent → ∃ bound : ℝ≥0∞, bound < (⊤ : ℝ≥0∞) ∧
    ∀ time ∈ Icc 0 horizon, eLpNorm (omega time) (ENNReal.ofReal exponent) volume ≤ bound
  zeroMean : ∀ time ∈ Icc 0 horizon, (∫ position, omega time position) = 0

theorem LocalCompactnessHypotheses.transportAnalyticHypotheses
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon) (index : ℕ) :
    TransportAnalyticHypotheses horizon (sequence index 0) (sequence index) := by
  refine ⟨(hypotheses.2.2 index).1, (hypotheses.2.2 index).2.1, ?_, ?_, ?_, ?_⟩
  · obtain ⟨radius, positive, supported⟩ := hypotheses.2.1
    exact ⟨radius, positive, supported index⟩
  · intro exponent bound time inside
    exact ((hypotheses.2.2 index).2.2.2 exponent bound time inside).1
  · intro exponent exponentBound
    obtain ⟨bound, finite, bounded⟩ := hypotheses.uniform_eLpNorm_bound horizonNonnegative exponentBound
    exact ⟨bound, finite, bounded index⟩
  · intro time inside
    exact ((hypotheses.2.2 index).2.2.1 time inside).2

theorem TransportAnalyticHypotheses.integrable
    {horizon : ℝ} {initial : Vorticity} {omega : Evolution}
    (hypotheses : TransportAnalyticHypotheses horizon initial omega)
    {time : ℝ} (inside : time ∈ Icc 0 horizon) : Integrable (omega time) :=
  memLp_one_iff_integrable.mp (by simpa using hypotheses.membership 1 le_rfl time inside)

end EulerNonuniqueness
