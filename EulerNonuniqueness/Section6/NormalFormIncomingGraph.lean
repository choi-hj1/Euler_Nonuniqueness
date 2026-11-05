import EulerNonuniqueness.General.StableAtBotUniqueness
import EulerNonuniqueness.Section6.NormalFormChart

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem normalForm_incoming_trajectory_on_graph
    {graph coordinate : ℝ → ℝ} {trajectory : ℝ → ℝ × ℝ} {constant radius : ℝ}
    (graphSmooth : ContDiffAt ℝ 1 graph 0) (coordinateContinuous : ContinuousAt coordinate 0)
    (graphZero : graph 0 = 0) (coordinateZero : coordinate 0 = 0)
    (radiusPositive : 0 < radius)
    (errorBound : ∀ point : ℝ × ℝ, |point.1| + |point.2| < radius →
      |(localNormalFormError 1 graph coordinate point).2| ≤
        constant * |(localNormalFormChart graph coordinate point).2| *
          (|(localNormalFormChart graph coordinate point).1| + |(localNormalFormChart graph coordinate point).2|))
    (limit : Tendsto trajectory atBot (𝓝 0))
    (equation : ∀ᶠ time : ℝ in atBot,
      HasDerivAt trajectory (shapeChartVelocity 1 (trajectory time)) time) :
    ∀ᶠ time : ℝ in atBot, (trajectory time).2 = graph (trajectory time).1 := by
  let stable := fun time => (trajectory time).2 - graph (trajectory time).1
  let remainder := fun time => (localNormalFormError 1 graph coordinate (trajectory time)).2
  let rate := 2 * Real.sqrt 2
  have ratePositive : 0 < rate := by dsimp only [rate]; positivity
  have stableContinuous : ContinuousAt (fun point : ℝ × ℝ => point.2 - graph point.1) 0 :=
    continuousAt_snd.sub (graphSmooth.continuousAt.comp (f := fun point : ℝ × ℝ => point.1) continuousAt_fst)
  have stableLimit : Tendsto stable atBot (𝓝 0) := by
    simpa only [stable, Function.comp_def, Prod.snd_zero, Prod.fst_zero, graphZero, sub_self] using
      stableContinuous.tendsto.comp limit
  have chartContinuous : ContinuousAt (localNormalFormChart graph coordinate) 0 :=
    (coordinateContinuous.comp (f := fun point : ℝ × ℝ => point.1) continuousAt_fst).prodMk stableContinuous
  have chartLimit : Tendsto (fun time => localNormalFormChart graph coordinate (trajectory time)) atBot (𝓝 0) := by
    simpa only [localNormalFormChart, Prod.fst_zero, Prod.snd_zero, graphZero, coordinateZero, sub_self,
      Prod.mk_zero_zero, Function.comp_def] using chartContinuous.tendsto.comp limit
  have factorContinuous : Continuous (fun point : ℝ × ℝ => constant * (|point.1| + |point.2|)) := by fun_prop
  have factorLimit := factorContinuous.continuousAt.tendsto.comp chartLimit
  have smallFactor := factorLimit.eventually
    (eventually_lt_nhds (show constant * (|(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2|) < rate / 2 by simpa using half_pos ratePositive))
  have sizeContinuous : Continuous (fun point : ℝ × ℝ => |point.1| + |point.2|) := by fun_prop
  have small := (sizeContinuous.continuousAt.tendsto.comp limit).eventually
    (eventually_lt_nhds (by simpa using radiusPositive : |(0 : ℝ × ℝ).1| + |(0 : ℝ × ℝ).2| < radius))
  have graphDifferentiable : ∀ᶠ unstable in 𝓝 (0 : ℝ), DifferentiableAt ℝ graph unstable :=
    (graphSmooth.eventually (by norm_num)).mono fun _ smooth => smooth.differentiableAt (by norm_num)
  have derivativeAlong := (continuous_fst.continuousAt.tendsto.comp limit).eventually graphDifferentiable
  obtain ⟨endpoint, before⟩ := eventually_atBot.mp (equation.and (small.and (smallFactor.and derivativeAlong)))
  have stableDerivative (time : ℝ) (inside : time ≤ endpoint) :
      HasDerivAt stable (-rate * stable time + remainder time) time := by
    have properties := before time inside
    have first : HasDerivAt (fun current => (trajectory current).1) (shapeChartVelocity 1 (trajectory time)).1 time :=
      (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time properties.1
    have second : HasDerivAt (fun current => (trajectory current).2) (shapeChartVelocity 1 (trajectory time)).2 time :=
      (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt time properties.1
    have actual := second.sub (properties.2.2.2.hasDerivAt.comp time first)
    convert actual using 1
    dsimp only [stable, remainder, rate, localNormalFormError, Prod.snd, Function.comp_def, one_mul, mul_one]
    ring
  have continuous : ContinuousOn stable (Iic endpoint) :=
    fun time member => (stableDerivative time member).continuousAt.continuousWithinAt
  have controlled (time : ℝ) (inside : time < endpoint) : |remainder time| ≤ rate / 2 * |stable time| := by
    have properties := before time inside.le
    have actual := errorBound (trajectory time) properties.2.1
    have smallFactor := mul_le_mul_of_nonneg_right properties.2.2.1.le (abs_nonneg (stable time))
    change constant * (|(localNormalFormChart graph coordinate (trajectory time)).1| +
      |(localNormalFormChart graph coordinate (trajectory time)).2|) * |stable time| ≤ rate / 2 * |stable time| at smallFactor
    exact actual.trans ((show constant * |(localNormalFormChart graph coordinate (trajectory time)).2| *
        (|(localNormalFormChart graph coordinate (trajectory time)).1| +
          |(localNormalFormChart graph coordinate (trajectory time)).2|) =
        constant * (|(localNormalFormChart graph coordinate (trajectory time)).1| +
          |(localNormalFormChart graph coordinate (trajectory time)).2|) * |stable time| by
            dsimp only [stable, localNormalFormChart]
            ring).le.trans smallFactor)
  have zero := EulerNonuniqueness.General.stable_solution_eq_zero_of_tendsto_atBot ratePositive continuous
    (fun time member => stableDerivative time member.le) controlled stableLimit
  filter_upwards [eventually_le_atBot endpoint] with time inside
  exact sub_eq_zero.mp (zero time inside)

end EulerNonuniqueness.Section6
