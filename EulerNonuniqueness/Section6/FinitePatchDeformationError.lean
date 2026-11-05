import EulerNonuniqueness.Section6.PatchPointFieldIdentity
import EulerNonuniqueness.Section6.PatchDeformationError
import EulerNonuniqueness.Section6.AffinePatchTrapping

noncomputable section

open Set MeasureTheory
open scoped symmDiff

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_nearCircle_trapping (flow : FiniteLiteralPatchFlow configuration)
    (time : ℝ) (index : Fin count) :
    Metric.ball (configuration.center index)
        (configuration.radius index * (1 - ‖flow.shape time index - standardCircleBanach‖)) ⊆ flow.domain time index ∧
      flow.domain time index ⊆ Metric.ball (configuration.center index)
        (configuration.radius index * (1 + ‖flow.shape time index - standardCircleBanach‖)) := by
  have small := (flow.nearby time index).trans_le (min_le_left _ _)
  exact ⟨affinePatchDomain_contains_ball _ (configuration.radius_pos index) _ small,
    affinePatchDomain_subset_ball _ (configuration.radius_pos index) _ small⟩

theorem domain_centroid_deformation_geometry (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    ‖flow.centroid time index - configuration.center index‖ ≤
        8 * configuration.radius index * ‖flow.shape time index - standardCircleBanach‖ ∧
      flow.domain time index ⊆ Metric.closedBall (flow.centroid time index) (2 * configuration.radius index) ∧
      volume.real (flow.domain time index ∆ Metric.ball (flow.centroid time index) (configuration.radius index)) ≤
        32 * Real.pi * configuration.radius index ^ 2 * ‖flow.shape time index - standardCircleBanach‖ := by
  have trapping := flow.domain_nearCircle_trapping time index
  exact Section6.patch_actual_centroid_geometry (flow.domain_isOpen time index).measurableSet
    (configuration.center index) (flow.centroid time index) (configuration.radius_pos index)
    (norm_nonneg (flow.shape time index - standardCircleBanach)) small
    trapping.1 trapping.2 (flow.domain_area inside index) (flow.domain_centroid_centered_integral inside index)

theorem component_biotSavart_relative_deformation (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (position : ℂ)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16)
    (separated : 4 * configuration.radius index ≤ ‖position - flow.centroid time index‖) :
    ‖biotSavart (flow.componentVorticity time index) position -
        (configuration.density index * (Real.pi * configuration.radius index ^ 2)) •
          biotSavartKernel (position - flow.centroid time index)‖ ≤
      128 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * ‖flow.shape time index - standardCircleBanach‖ /
          (Real.pi * ‖position - flow.centroid time index‖ ^ 3) := by
  have trapping := flow.domain_nearCircle_trapping time index
  exact Section6.biotSavart_patch_relative_deformation_bound (flow.domain_isOpen time index).measurableSet
    (configuration.center index) (flow.centroid time index) position (configuration.radius_pos index)
    (norm_nonneg (flow.shape time index - standardCircleBanach)) small trapping.1 trapping.2 (flow.domain_area inside index)
    (flow.domain_centroid_centered_integral inside index) separated (configuration.density index)

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
