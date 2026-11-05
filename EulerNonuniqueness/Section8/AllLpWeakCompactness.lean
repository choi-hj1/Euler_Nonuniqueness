import EulerNonuniqueness.General.LpWeakBounds
import EulerNonuniqueness.Section8.SupportedWeakCompactness

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EulerNonuniqueness

theorem LocalCompactnessHypotheses.exists_allLp_weakL2_vorticity_subsequence
    {horizon : ℝ} {initial : Vorticity} {sequence : ℕ → Evolution}
    (hypotheses : LocalCompactnessHypotheses horizon initial sequence)
    (horizonNonnegative : 0 ≤ horizon)
    (parameters : ℕ → ℕ × Icc (0 : ℝ) horizon) :
    ∃ radius : ℝ, 0 < radius ∧ ∃ limit : Vorticity,
      HasCompactSupport limit ∧ Function.support limit ⊆ Metric.closedBall 0 radius ∧
      (∫ position, limit position) = 0 ∧
      (∀ exponent : ℝ, 1 ≤ exponent → MemLp limit (ENNReal.ofReal exponent) volume) ∧
      ∃ subsequence : ℕ → ℕ, StrictMono subsequence ∧ ∀ test : Vorticity,
        MemLp test 2 volume → Tendsto
          (fun index => ∫ position, sequence (parameters (subsequence index)).1
            (parameters (subsequence index)).2 position * test position)
          atTop (𝓝 (∫ position, limit position * test position)) := by
  obtain ⟨radius, positive, limit, limitMember, limitIntegrable, compact,
    supported, meanZero, subsequence, increasing, weak⟩ :=
    hypotheses.exists_supported_weakL2_vorticity_subsequence horizonNonnegative parameters
  refine ⟨radius, positive, limit, compact, supported, meanZero, ?_, subsequence, increasing, weak⟩
  intro exponent exponentBound
  obtain ⟨bound, finite, bounded⟩ := hypotheses.uniform_eLpNorm_bound horizonNonnegative exponentBound
  have normBound : eLpNorm limit (ENNReal.ofReal exponent) volume ≤ bound :=
    eLpNorm_le_of_weakL2_tendsto_functions
      (fun index => (hypotheses.2.2 (parameters (subsequence index)).1).2.1.1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property)
      limitMember (by exact_mod_cast ENNReal.ofReal_le_ofReal exponentBound)
      (fun index => bounded (parameters (subsequence index)).1
        (parameters (subsequence index)).2 (parameters (subsequence index)).2.property) weak
  exact ⟨limitMember.aestronglyMeasurable, normBound.trans_lt finite⟩

end EulerNonuniqueness
