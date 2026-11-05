import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Tactic

noncomputable section

open Set MeasureTheory Filter Function
open scoped Topology ENNReal

namespace EulerNonuniqueness.General

theorem indicator_sum_eq_component_of_separated_supports
    {Index Domain : Type*} [Fintype Index] [MetricSpace Domain]
    (component : Index → Domain → ℝ) (anchor oldAnchor : Index → Domain)
    (radius : Index → ℝ) (selected : Index)
    (radiusPositive : ∀ index, 0 < radius index)
    (anchorNear : ∀ index, dist (anchor index) (oldAnchor index) < radius index)
    (separated : ∀ other, other ≠ selected →
      2 * radius selected + 2 * radius other < dist (oldAnchor selected) (oldAnchor other))
    (supported : ∀ index, support (component index) ⊆ Metric.closedBall (anchor index) (radius index)) :
    (Metric.closedBall (oldAnchor selected) (2 * radius selected)).indicator
      (fun position => ∑ index, component index position) = component selected := by
  classical
  funext position
  have localDistance (index : Index) (nonzero : component index position ≠ 0) :
      dist position (oldAnchor index) < 2 * radius index := by
    have actual := supported index nonzero
    have triangle := dist_triangle position (anchor index) (oldAnchor index)
    have nearby := anchorNear index
    change dist position (anchor index) ≤ radius index at actual
    linarith
  by_cases inside : position ∈ Metric.closedBall (oldAnchor selected) (2 * radius selected)
  · rw [Set.indicator_of_mem inside]
    apply Finset.sum_eq_single selected
    · intro other _ different
      by_contra nonzero
      have actual := localDistance other nonzero
      have gap := separated other different
      have triangle := dist_triangle (oldAnchor selected) position (oldAnchor other)
      change dist position (oldAnchor selected) ≤ 2 * radius selected at inside
      rw [dist_comm (oldAnchor selected) position] at triangle
      linarith
    · simp
  · rw [Set.indicator_of_not_mem inside]
    symm
    by_contra nonzero
    exact inside (le_of_lt (localDistance selected nonzero))

theorem tendsto_eLpNorm_component_sub_of_localized_finite_sum
    {Index Domain : Type*} [Fintype Index] [MetricSpace Domain] [MeasurableSpace Domain]
    {measure : Measure Domain} {times : Set ℝ} {base : ℝ} (baseInside : base ∈ times)
    {component : Index → ℝ → Domain → ℝ} {anchor : Index → ℝ → Domain}
    {radius : Index → ℝ} {exponent : ℝ≥0∞} (selected : Index)
    (radiusPositive : ∀ index, 0 < radius index)
    (anchorContinuous : ∀ index, ContinuousWithinAt (anchor index) times base)
    (separated : ∀ other, other ≠ selected →
      2 * radius selected + 2 * radius other < dist (anchor selected base) (anchor other base))
    (supported : ∀ time ∈ times, ∀ index,
      support (component index time) ⊆ Metric.closedBall (anchor index time) (radius index))
    (totalConverges : Tendsto
      (fun time => eLpNorm (fun position =>
        (∑ index, component index time position) - ∑ index, component index base position) exponent measure)
      (𝓝[times] base) (𝓝 0)) :
    Tendsto (fun time => eLpNorm (fun position =>
      component selected time position - component selected base position) exponent measure)
      (𝓝[times] base) (𝓝 0) := by
  classical
  let region := Metric.closedBall (anchor selected base) (2 * radius selected)
  have baseIdentity : region.indicator (fun position => ∑ index, component index base position) =
      component selected base :=
    indicator_sum_eq_component_of_separated_supports (fun index => component index base)
      (fun index => anchor index base) (fun index => anchor index base) radius selected radiusPositive
      (fun index => by simpa only [dist_self] using radiusPositive index) separated (supported base baseInside)
  have anchorsNear : ∀ᶠ time in 𝓝[times] base,
      ∀ index, dist (anchor index time) (anchor index base) < radius index := by
    rw [Filter.eventually_all]
    intro index
    exact (Metric.tendsto_nhds.mp (anchorContinuous index)) (radius index) (radiusPositive index)
  have componentBound : ∀ᶠ time in 𝓝[times] base,
      eLpNorm (fun position => component selected time position - component selected base position) exponent measure ≤
        eLpNorm (fun position =>
          (∑ index, component index time position) - ∑ index, component index base position) exponent measure := by
    filter_upwards [anchorsNear, self_mem_nhdsWithin] with time near inside
    have identity : region.indicator (fun position => ∑ index, component index time position) =
        component selected time :=
      indicator_sum_eq_component_of_separated_supports (fun index => component index time)
        (fun index => anchor index time) (fun index => anchor index base) radius selected radiusPositive
        near separated (supported time inside)
    have differenceIdentity : (fun position => component selected time position - component selected base position) =
        region.indicator (fun position =>
          (∑ index, component index time position) - ∑ index, component index base position) := by
      rw [Set.indicator_sub, identity, baseIdentity]
    rw [differenceIdentity]
    exact eLpNorm_indicator_le _
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds totalConverges
    (Filter.Eventually.of_forall (fun _ => bot_le)) componentBound

end EulerNonuniqueness.General
