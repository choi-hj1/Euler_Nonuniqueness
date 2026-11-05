import EulerNonuniqueness.General.TaylorRemainder
import Mathlib.Topology.UniformSpace.HeineCantor

noncomputable section

open Set Metric

namespace EulerNonuniqueness

theorem uniform_image_dist_near_compact {Domain Target : Type*}
    [PseudoMetricSpace Domain] [PseudoMetricSpace Target]
    {region : Set Domain} (compact : IsCompact region) {function : Domain → Target}
    (continuous : Continuous function) {error : ℝ} (positive : 0 < error) :
    ∃ radius > 0, ∀ first ∈ region, ∀ second,
      dist first second < radius → dist (function first) (function second) < error := by
  have entourage := compact.uniformContinuousAt_of_continuousAt function
    (fun _ _ => continuous.continuousAt) (Metric.dist_mem_uniformity positive)
  obtain ⟨radius, radiusPositive, close⟩ := Metric.mem_uniformity_dist.mp entourage
  exact ⟨radius, radiusPositive, fun first inside second near => close near inside⟩

theorem uniform_taylor_remainder_near_compact {Parameter Domain Target : Type*}
    [PseudoMetricSpace Parameter] [NormedAddCommGroup Domain] [NormedSpace ℝ Domain]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    {function : Parameter → Domain → Target}
    {derivative : Parameter → Domain → Domain →L[ℝ] Target}
    (continuous : Continuous (fun point : Parameter × Domain => derivative point.1 point.2))
    (differentiable : ∀ parameter position, HasFDerivAt (function parameter) (derivative parameter position) position)
    {region : Set (Parameter × Domain)} (compact : IsCompact region)
    {error : ℝ} (positive : 0 < error) :
    ∃ radius > 0, ∀ parameter position, (parameter, position) ∈ region →
      ∀ increment, ‖increment‖ < radius →
        ‖function parameter (position + increment) - function parameter position -
          derivative parameter position increment‖ ≤ error * ‖increment‖ := by
  obtain ⟨radius, radiusPositive, close⟩ := uniform_image_dist_near_compact compact continuous positive
  refine ⟨radius, radiusPositive, ?_⟩
  intro parameter position inside increment small
  have estimate := norm_taylor_remainder_le (convex_ball position radius)
    (fun point _ => differentiable parameter point) (mem_ball_self radiusPositive)
    (show position + increment ∈ ball position radius by simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left] using small)
    (error := error) (fun point pointInside => by
      have near : dist (parameter, position) (parameter, point) < radius := by
        simpa only [mem_ball, Prod.dist_eq, dist_self, max_eq_right dist_nonneg, dist_comm] using pointInside
      have bound := close (parameter, position) inside (parameter, point) near
      simpa only [dist_eq_norm, norm_sub_rev] using bound.le)
  simpa only [add_sub_cancel_left] using estimate

end EulerNonuniqueness
