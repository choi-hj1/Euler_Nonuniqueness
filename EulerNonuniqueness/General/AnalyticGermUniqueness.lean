import Mathlib.Analysis.Analytic.IsolatedZeros

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem analytic_germ_eq_of_eq_along_punctured_curve
    {Index : Type*} {filter : Filter Index} [NeBot filter]
    {first second : ℝ → ℝ} {center : ℝ} {curve : Index → ℝ}
    (firstAnalytic : AnalyticAt ℝ first center)
    (secondAnalytic : AnalyticAt ℝ second center)
    (punctured : Tendsto curve filter (𝓝[≠] center))
    (agreement : ∀ᶠ parameter in filter, first (curve parameter) = second (curve parameter)) :
    first =ᶠ[𝓝 center] second := by
  rcases firstAnalytic.eventually_eq_or_eventually_ne secondAnalytic with equal | different
  · exact equal
  · obtain ⟨parameter, different, equal⟩ := ((punctured.eventually different).and agreement).exists
    exact (different equal).elim

end EulerNonuniqueness.General
