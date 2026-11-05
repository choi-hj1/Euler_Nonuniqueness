import Mathlib

namespace EulerNonuniqueness.General

open Filter
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem eventually_fderiv_annihilates_stationary_subspace
    (function : Space → Space) (projection : Space →L[ℝ] Space)
    (regular : ∀ᶠ value in 𝓝 (0 : Space), DifferentiableAt ℝ function value)
    (stationary : ∀ᶠ value in 𝓝 (0 : Space), function (projection value) = 0) :
    ∀ᶠ value in 𝓝 (0 : Space), (fderiv ℝ function (projection value)).comp projection = 0 := by
  have projectionLimit : Tendsto projection (𝓝 (0 : Space)) (𝓝 (0 : Space)) := by
    simpa only [map_zero] using projection.continuous.tendsto (0 : Space)
  filter_upwards [projectionLimit.eventually regular, stationary.eventually_nhds] with value differentiable locallyZero
  have actual := differentiable.hasFDerivAt.comp value (projection.hasFDerivAt (x := value))
  have zero : HasFDerivAt (fun point => function (projection point)) (0 : Space →L[ℝ] Space) value :=
    (hasFDerivAt_const (0 : Space) value).congr_of_eventuallyEq locallyZero
  exact actual.unique zero

end EulerNonuniqueness.General
