import EulerNonuniqueness.Section3.FinitePatchBounds
import EulerNonuniqueness.Section8.BoundedVorticityContinuity

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

namespace EulerNonuniqueness.Paper

theorem norm_patchVorticity_le_sum {count : ℕ} (scales : Scales) (motion : PatchMotion count)
    (time : ℝ) (position : Plane) :
    ‖patchVorticity scales motion time position‖ ≤ ∑ index : Fin count, ∑ patch : Fin 4,
      ‖patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro index _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro patch _
  exact norm_indicator_le_norm_self _ _

theorem FinitePatchEvolution.continuousInLp_vorticity
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon)
    {exponent : ℝ} (exponentBound : 1 ≤ exponent) :
    ContinuousInLpOn horizon (ENNReal.ofReal exponent) (patchVorticity scales motion) := by
  apply continuousInLpOn_of_uniform_bound_of_tendsto_one
    (bound := ∑ index : Fin count, ∑ patch : Fin 4,
      ‖patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4‖)
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) exponentBound
  · intro time inside
    have properties := evolution.2.2.2.1 time inside
    exact patchVorticity_memLp scales motion time (fun index patch => (properties index patch).1)
      (fun index patch => (properties index patch).2.1) _
  · exact fun time _ position => norm_patchVorticity_le_sum scales motion time position
  · exact fun time inside => (evolution.2.2.1 time inside).2

end EulerNonuniqueness.Paper
