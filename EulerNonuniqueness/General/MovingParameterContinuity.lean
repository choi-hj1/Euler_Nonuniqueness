import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Abel

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem continuousAt_moving_parameter_of_frozen
    {Parameter Target : Type*} [PseudoMetricSpace Parameter] [NormedAddCommGroup Target]
    {function : Parameter → ℝ → Target} {parameter : ℝ → Parameter}
    {time constant : ℝ} {admissible : Set Parameter}
    (parameterContinuous : ContinuousAt parameter time)
    (initialInside : parameter time ∈ admissible)
    (nearbyInside : ∀ᶠ current in 𝓝 time, parameter current ∈ admissible)
    (variation : ∀ᶠ current in 𝓝 time,
      ∀ first ∈ admissible, ∀ second ∈ admissible,
      ‖function first current - function second current‖ ≤ constant * dist first second)
    (frozenContinuous : ContinuousAt (fun current => function (parameter time) current) time) :
    ContinuousAt (fun current => function (parameter current) current) time := by
  have vanishes : Tendsto
      (fun current => function (parameter current) current - function (parameter time) current)
      (𝓝 time) (𝓝 0) := by
    have bound : ∀ᶠ current in 𝓝 time,
        ‖function (parameter current) current - function (parameter time) current‖ ≤
          constant * dist (parameter current) (parameter time) := by
      filter_upwards [variation, nearbyInside] with current estimate inside
      exact estimate _ inside _ initialInside
    have envelope : Tendsto (fun current => constant * dist (parameter current) (parameter time)) (𝓝 time) (𝓝 0) := by
      simpa only [dist_self, mul_zero] using
        (parameterContinuous.tendsto.dist
          (tendsto_const_nhds : Tendsto (fun _ : ℝ => parameter time) (𝓝 time) (𝓝 (parameter time)))).const_mul constant
    exact squeeze_zero_norm' bound envelope
  have composed := frozenContinuous.tendsto.add vanishes
  have identity :
      (fun current => function (parameter time) current +
        (function (parameter current) current - function (parameter time) current)) =
      (fun current => function (parameter current) current) := by
    funext current
    abel
  rw [identity] at composed
  simpa only [add_zero] using composed

end EulerNonuniqueness.General
