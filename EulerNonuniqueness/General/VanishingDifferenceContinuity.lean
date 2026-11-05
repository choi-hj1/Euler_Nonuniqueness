import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Tactic.Abel

open Filter
open scoped Topology

namespace EulerNonuniqueness.General

theorem continuousAt_of_vanishing_difference {Domain Target : Type*}
    [TopologicalSpace Domain] [NormedAddCommGroup Target]
    {first second : Domain → Target} {point : Domain}
    (value : first point = second point)
    (continuous : ContinuousAt second point)
    (vanishes : Tendsto (fun current => first current - second current) (𝓝 point) (𝓝 0)) :
    ContinuousAt first point := by
  have result := continuous.tendsto.add vanishes
  have identity : (fun current => second current + (first current - second current)) = first := by
    funext current
    abel
  rw [identity, add_zero, ← value] at result
  exact result

end EulerNonuniqueness.General
