import EulerNonuniqueness.Section3.ContourLocalEvolution

open Set Metric
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable section

local instance contourStabilityHolderNormedSpace : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance contourStabilityC1NormedSpace : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph

set_option maxHeartbeats 1000000 in
theorem contour_evolution_continuous_dependence
    {first second : ℝ → PeriodicC1HolderHalf} {lower upper radius : ℝ}
    (radius_nonneg : 0 ≤ radius)
    (radius_small : radius < min 1 (2 / (3 * Real.pi)))
    (first_continuous : ContinuousOn first (Icc lower upper))
    (second_continuous : ContinuousOn second (Icc lower upper))
    (first_equation : ∀ time ∈ Ico lower upper,
      HasDerivAt first (extendedContourVelocity (first time)) time)
    (second_equation : ∀ time ∈ Ico lower upper,
      HasDerivAt second (extendedContourVelocity (second time)) time)
    (first_near : ∀ time ∈ Ico lower upper, ‖first time - standardCircleBanach‖ ≤ radius)
    (second_near : ∀ time ∈ Ico lower upper, ‖second time - standardCircleBanach‖ ≤ radius) :
    ∀ time ∈ Icc lower upper,
      ‖first time - second time‖ ≤ ‖first lower - second lower‖ *
        Real.exp (contourVelocityBanachLipschitzConstant radius * (time - lower)) := by
  let constant : NNReal := ⟨contourVelocityBanachLipschitzConstant radius,
    contourVelocityBanachLipschitzConstant_nonneg radius_nonneg radius_small⟩
  have estimate := dist_le_of_trajectories_ODE_of_mem
    (K := constant) (v := fun _ => extendedContourVelocity)
    (s := fun _ => closedBall standardCircleBanach radius)
    (fun _ _ => extendedContourVelocity_lipschitzOn radius_nonneg radius_small)
    first_continuous (fun time time_mem => (first_equation time time_mem).hasDerivWithinAt)
    (fun time time_mem => by
      change dist (first time) standardCircleBanach ≤ radius
      rw [dist_eq_norm (first time) standardCircleBanach]
      exact first_near time time_mem)
    second_continuous (fun time time_mem => (second_equation time time_mem).hasDerivWithinAt)
    (fun time time_mem => by
      change dist (second time) standardCircleBanach ≤ radius
      rw [dist_eq_norm (second time) standardCircleBanach]
      exact second_near time time_mem)
    (δ := ‖first lower - second lower‖)
    (by rw [dist_eq_norm (first lower) (second lower)])
  intro time time_mem
  have bound := estimate time time_mem
  rw [dist_eq_norm (first time) (second time)] at bound
  exact bound

end

end EulerNonuniqueness.Paper
