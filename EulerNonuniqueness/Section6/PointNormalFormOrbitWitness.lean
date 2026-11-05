import EulerNonuniqueness.Section6.NormalFormOrbitCompatibility
import EulerNonuniqueness.Section6.PointNormalFormMemoryRemainder

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem exists_uniform_pointNormalForm_memory_orbit_compatible :
    ∃ graph coordinate : ℝ → ℝ,
      AnalyticAt ℝ graph 0 ∧ graph 0 = 0 ∧ HasDerivAt graph 0 0 ∧
      ContDiffAt ℝ 2 coordinate 0 ∧ coordinate 0 = 0 ∧ HasDerivAt coordinate 1 0 ∧
      ∃ constant ≥ (0 : ℝ), ∃ radius > (0 : ℝ),
      (∀ frequency : ℝ, ∀ first second : ℝ × ℝ,
        |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
        let firstChart := localNormalFormChart graph coordinate first
        let secondChart := localNormalFormChart graph coordinate second
        ‖localNormalFormError frequency graph coordinate first - localNormalFormError frequency graph coordinate second‖ ≤
          constant * |frequency| * (|firstChart.1 - secondChart.1| + |firstChart.2 - secondChart.2|) *
            (|firstChart.2 - secondChart.2| + |secondChart.1| + |secondChart.2|)) ∧
      (∀ orbit : EulerNonuniqueness.Paper.SeparatingOrbit,
        EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit →
        ∀ᶠ time : ℝ in atBot,
          EulerNonuniqueness.Paper.orbitStableShape orbit time = graph (EulerNonuniqueness.Paper.orbitUnstableShape orbit time)) := by
  obtain ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, constant, constantNonnegative, radius, radiusPositive, bound⟩ :=
    exists_uniform_localNormalForm_relative_coordinates
  refine ⟨graph, coordinate, graphAnalytic, graphZero, graphDerivative, coordinateSmooth, coordinateZero,
    coordinateDerivative, 2 * constant, by positivity, radius, radiusPositive, ?_, ?_⟩
  · intro frequency first second firstSmall secondSmall
    dsimp only
    apply (bound frequency first second firstSmall secondSmall).trans
    have actual := mul_le_mul_of_nonneg_left
      (graded_saddle_difference_budget (localNormalFormChart graph coordinate first).1
        (localNormalFormChart graph coordinate first).2 (localNormalFormChart graph coordinate second).1
        (localNormalFormChart graph coordinate second).2)
      (mul_nonneg constantNonnegative (abs_nonneg frequency))
    convert actual using 1 <;> ring
  · intro orbit normalized
    apply normalizedSeparatingOrbit_on_normalForm_graph
      (graphAnalytic.contDiffAt (n := 1)) coordinateSmooth.continuousAt graphZero coordinateZero radiusPositive
      (constant := 2 * constant) (orbit := orbit) (normalized := normalized)
    apply localNormalForm_stable_bound_of_graded graphZero coordinateZero constantNonnegative radiusPositive
    intro first second firstSmall secondSmall
    have actual := bound 1 first second firstSmall secondSmall
    simpa only [abs_one, mul_one] using actual

end EulerNonuniqueness.Section6
