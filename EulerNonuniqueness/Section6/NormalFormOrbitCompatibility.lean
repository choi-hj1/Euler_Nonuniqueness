import EulerNonuniqueness.Section6.NormalFormIncomingGraph
import EulerNonuniqueness.Section6.NormalFormRelativeCoordinates
import EulerNonuniqueness.Section6.NormalizedOrbitIncomingDynamics

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem localNormalFormError_at_zero {graph coordinate : ℝ → ℝ}
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0) :
    localNormalFormError 1 graph coordinate 0 = 0 := by
  simp [localNormalFormError, shapeChartVelocity_zero, graphZero, coordinateZero]

theorem localNormalForm_stable_bound_of_graded {graph coordinate : ℝ → ℝ} {constant radius : ℝ}
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (constantNonnegative : 0 ≤ constant) (radiusPositive : 0 < radius)
    (graded : ∀ first second : ℝ × ℝ,
      |first.1| + |first.2| < radius → |second.1| + |second.2| < radius →
      let firstChart := localNormalFormChart graph coordinate first
      let secondChart := localNormalFormChart graph coordinate second
      ‖localNormalFormError 1 graph coordinate first - localNormalFormError 1 graph coordinate second‖ ≤
        constant * ((|firstChart.2| + |secondChart.2|) * |firstChart.1 - secondChart.1| +
          (|firstChart.1| + |secondChart.1| + |firstChart.2| + |secondChart.2|) * |firstChart.2 - secondChart.2|)) :
    ∀ point : ℝ × ℝ, |point.1| + |point.2| < radius →
      |(localNormalFormError 1 graph coordinate point).2| ≤
        (2 * constant) * |(localNormalFormChart graph coordinate point).2| *
          (|(localNormalFormChart graph coordinate point).1| + |(localNormalFormChart graph coordinate point).2|) := by
  have chartZero : localNormalFormChart graph coordinate 0 = 0 := by
    simp [localNormalFormChart, graphZero, coordinateZero]
  intro point small
  have actual := graded point 0 small (by simpa using radiusPositive)
  dsimp only at actual
  rw [localNormalFormError_at_zero graphZero coordinateZero, sub_zero, chartZero] at actual
  simp only [Prod.fst_zero, Prod.snd_zero, abs_zero, add_zero, zero_add, sub_zero] at actual
  have component : |(localNormalFormError 1 graph coordinate point).2| ≤
      ‖localNormalFormError 1 graph coordinate point‖ := by
    simpa only [Real.norm_eq_abs] using norm_snd_le (localNormalFormError 1 graph coordinate point)
  apply component.trans (actual.trans _)
  have extra := mul_nonneg constantNonnegative (sq_nonneg |(localNormalFormChart graph coordinate point).2|)
  nlinarith

theorem normalizedSeparatingOrbit_on_normalForm_graph
    {graph coordinate : ℝ → ℝ} {constant radius : ℝ}
    (graphSmooth : ContDiffAt ℝ 1 graph 0) (coordinateContinuous : ContinuousAt coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (radiusPositive : 0 < radius)
    (errorBound : ∀ point : ℝ × ℝ, |point.1| + |point.2| < radius →
      |(localNormalFormError 1 graph coordinate point).2| ≤
        constant * |(localNormalFormChart graph coordinate point).2| *
          (|(localNormalFormChart graph coordinate point).1| + |(localNormalFormChart graph coordinate point).2|))
    (orbit : EulerNonuniqueness.Paper.SeparatingOrbit)
    (normalized : EulerNonuniqueness.Paper.IsNormalizedSeparatingOrbit orbit) :
    ∀ᶠ time : ℝ in atBot,
      EulerNonuniqueness.Paper.orbitStableShape orbit time = graph (EulerNonuniqueness.Paper.orbitUnstableShape orbit time) := by
  exact normalForm_incoming_trajectory_on_graph graphSmooth coordinateContinuous graphZero coordinateZero radiusPositive
    errorBound (EulerNonuniqueness.Paper.normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized)
    (EulerNonuniqueness.Paper.normalizedSeparatingOrbit_eventually_shape_equation orbit normalized)

end EulerNonuniqueness.Section6
