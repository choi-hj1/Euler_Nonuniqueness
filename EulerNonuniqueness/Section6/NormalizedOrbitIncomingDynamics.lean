import EulerNonuniqueness.Section6.HalfDiagonalShapeDynamics
import EulerNonuniqueness.Section5.CascadeStatement

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

open EulerNonuniqueness.Section6

theorem normalizedSeparatingOrbit_shape_tendsto_zero (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    Tendsto (fun time => (orbitUnstableShape orbit time, orbitStableShape orbit time)) atBot (𝓝 0) := by
  rcases normalized with ⟨_, _, _, ratioIncoming, angleIncoming, _⟩
  have radial := (ratioIncoming.sub_const rhombusRatio).div_const rhombusRatio
  have angular := (angleIncoming.sub_const Real.pi).div_const (Real.sqrt 2)
  have unstable := (radial.add angular).div_const 2
  have stable := (radial.sub angular).div_const 2
  simpa only [orbitUnstableShape, orbitStableShape, orbitRadialShape, orbitAngularShape,
    sub_self, zero_div, zero_add, Prod.mk_zero_zero] using unstable.prodMk_nhds stable

theorem normalizedSeparatingOrbit_eventually_upper (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∀ᶠ time : ℝ in atBot, 0 < (orbit.negative time / orbit.positive time).im := by
  rcases normalized with ⟨_, _, _, _, angleIncoming, _⟩
  have lower := angleIncoming.eventually (eventually_gt_nhds (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi))
  have upper := angleIncoming.eventually (eventually_lt_nhds (by linarith [Real.pi_pos] : Real.pi < 2 * Real.pi))
  filter_upwards [lower, upper] with time lower upper
  have argPositive : 0 < Complex.arg (orbit.negative time / orbit.positive time) := by linarith
  have argBelow : Complex.arg (orbit.negative time / orbit.positive time) < Real.pi := by linarith
  have nonzero : orbit.negative time / orbit.positive time ≠ 0 := by
    intro zero
    rw [zero, Complex.arg_zero] at argPositive
    exact lt_irrefl 0 argPositive
  rw [← Complex.norm_mul_sin_arg]
  exact mul_pos (norm_pos_iff.mpr nonzero) (Real.sin_pos_of_pos_of_lt_pi argPositive argBelow)

theorem normalizedSeparatingOrbit_shape_hasDerivAt_of_upper (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) (time : ℝ)
    (upper : 0 < (orbit.negative time / orbit.positive time).im)
    (small : |orbitUnstableShape orbit time| + |orbitStableShape orbit time| ≤ 1 / 4) :
    HasDerivAt (fun current => (orbitUnstableShape orbit current, orbitStableShape orbit current))
      (shapeChartVelocity 1 (orbitUnstableShape orbit time, orbitStableShape orbit time)) time := by
  have properties := normalized.2.1 time
  have positiveDerivative : HasDerivAt orbit.positive
      (positivePointVelocity 1 (orbit.positive time) (orbit.negative time)) time := by
    simpa only [positivePointVelocity, Complex.ofReal_one, mul_one] using properties.2.2.1
  have negativeDerivative : HasDerivAt orbit.negative
      (negativePointVelocity 1 (orbit.positive time) (orbit.negative time)) time := by
    simpa only [negativePointVelocity, Complex.ofReal_one, mul_one] using properties.2.2.2
  have actual := halfDiagonalShape_unforced_hasDerivAt
    (by rw [properties.1]; norm_num) upper small positiveDerivative negativeDerivative
  simpa only [properties.1, div_one] using actual

theorem normalizedSeparatingOrbit_eventually_shape_equation (orbit : SeparatingOrbit)
    (normalized : IsNormalizedSeparatingOrbit orbit) :
    ∀ᶠ time : ℝ in atBot,
      HasDerivAt (fun current => (orbitUnstableShape orbit current, orbitStableShape orbit current))
        (shapeChartVelocity 1 (orbitUnstableShape orbit time, orbitStableShape orbit time)) time := by
  have limit := normalizedSeparatingOrbit_shape_tendsto_zero orbit normalized
  have sizeContinuous : Continuous (fun point : ℝ × ℝ => |point.1| + |point.2|) := by fun_prop
  have small := (sizeContinuous.continuousAt.tendsto.comp limit).eventually
    (eventually_lt_nhds (by norm_num : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < 1 / 4))
  filter_upwards [normalizedSeparatingOrbit_eventually_upper orbit normalized, small] with time upper small
  exact normalizedSeparatingOrbit_shape_hasDerivAt_of_upper orbit normalized time upper small.le

end EulerNonuniqueness.Paper
