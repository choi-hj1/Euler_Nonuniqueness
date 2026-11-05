import EulerNonuniqueness.Section6.NormalFormInverseMatching
import EulerNonuniqueness.Section6.NormalizedOrbitIncomingDynamics

noncomputable section

open Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Paper

theorem normalizedSeparatingOrbit_normalForm_entry_control
    {graph coordinate : ℝ → ℝ}
    (graphSmooth : ContDiffAt ℝ 2 graph 0) (coordinateSmooth : ContDiffAt ℝ 2 coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (graphDerivative : HasDerivAt graph 0 0) (coordinateDerivative : HasDerivAt coordinate 1 0)
    (orbit : SeparatingOrbit) (normalized : IsNormalizedSeparatingOrbit orbit)
    (compatible : ∀ᶠ time : ℝ in atBot, orbitStableShape orbit time = graph (orbitUnstableShape orbit time)) :
    ∃ radius > (0 : ℝ), ∃ constant ≥ (1 : ℝ), ∀ᶠ incomingTime : ℝ in atBot,
    ∀ point : ℝ × ℝ, |point.1| + |point.2| < radius →
      |point.1 - orbitUnstableShape orbit incomingTime| + |point.2 - orbitStableShape orbit incomingTime| ≤
        constant * (|coordinate point.1 - coordinate (orbitUnstableShape orbit incomingTime)| +
          |point.2 - graph point.1|) := by
  obtain ⟨radius, radiusPositive, constant, constantOne, inverseBound⟩ :=
    localNormalFormChart_exists_uniform_inverse_lipschitz graphSmooth coordinateSmooth graphZero coordinateZero
      graphDerivative coordinateDerivative
  have limit := normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized
  have sizeContinuous : Continuous (fun point : ℝ × ℝ => |point.1| + |point.2|) := by fun_prop
  have small := (sizeContinuous.continuousAt.tendsto.comp limit).eventually
    (eventually_lt_nhds (by simpa using radiusPositive : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < radius))
  refine ⟨radius, radiusPositive, constant, constantOne, ?_⟩
  filter_upwards [compatible, small] with incomingTime graphIdentity small
  intro point pointSmall
  have actual := inverseBound point (orbitUnstableShape orbit incomingTime, orbitStableShape orbit incomingTime)
    pointSmall small
  have chartBound : ‖localNormalFormChart graph coordinate point -
      localNormalFormChart graph coordinate (orbitUnstableShape orbit incomingTime, orbitStableShape orbit incomingTime)‖ ≤
      |coordinate point.1 - coordinate (orbitUnstableShape orbit incomingTime)| + |point.2 - graph point.1| := by
    simp only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, localNormalFormChart, graphIdentity,
      sub_self, sub_zero, Real.norm_eq_abs]
    exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _))
  exact actual.trans (mul_le_mul_of_nonneg_left chartBound (by linarith))

end EulerNonuniqueness.Section6
