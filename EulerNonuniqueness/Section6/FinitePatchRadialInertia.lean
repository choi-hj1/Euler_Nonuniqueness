import EulerNonuniqueness.Section6.PatchCentroidRadialInertia
import EulerNonuniqueness.Section6.FinitePatchDeformationError

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem domain_centered_radial_second_moment_bound_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (center : ℂ) {error : ℝ} (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (lower : Metric.ball center (configuration.radius index * (1 - error)) ⊆ flow.domain time index)
    (upper : flow.domain time index ⊆ Metric.ball center (configuration.radius index * (1 + error))) :
    |(∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
      Real.pi * configuration.radius index ^ 4 / 2| ≤
      76 * Real.pi * configuration.radius index ^ 4 * error ^ 2 := by
  exact Section6.centroid_patch_radial_inertia_deformation_bound (flow.domain_isOpen time index).measurableSet
    center (flow.centroid time index) (configuration.radius_pos index) errorNonnegative errorSmall
    lower upper (flow.domain_area inside index) (flow.domain_centroid_centered_integral inside index)

theorem domain_centered_radial_second_moment_deformation_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    |(∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
      Real.pi * configuration.radius index ^ 4 / 2| ≤
      76 * Real.pi * configuration.radius index ^ 4 * ‖flow.shape time index - standardCircleBanach‖ ^ 2 := by
  have trapping := flow.domain_nearCircle_trapping time index
  exact flow.domain_centered_radial_second_moment_bound_of_trapping inside index
    (configuration.center index) (norm_nonneg _) small trapping.1 trapping.2

theorem domain_weighted_radial_second_moment_bound_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (center : ℂ) {error : ℝ} (errorNonnegative : 0 ≤ error) (errorSmall : error ≤ 1 / 16)
    (lower : Metric.ball center (configuration.radius index * (1 - error)) ⊆ flow.domain time index)
    (upper : flow.domain time index ⊆ Metric.ball center (configuration.radius index * (1 + error))) :
    |configuration.density index *
      ((∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
        Real.pi * configuration.radius index ^ 4 / 2)| ≤
      76 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * error ^ 2 := by
  rw [abs_mul]
  have estimate := mul_le_mul_of_nonneg_left
    (flow.domain_centered_radial_second_moment_bound_of_trapping inside index center
      errorNonnegative errorSmall lower upper) (abs_nonneg (configuration.density index))
  exact estimate.trans_eq (by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius index ^ 2 by positivity)]
    ring)

theorem domain_weighted_radial_second_moment_deformation_bound (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count)
    (small : ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    |configuration.density index *
      ((∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) -
        Real.pi * configuration.radius index ^ 4 / 2)| ≤
      76 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * ‖flow.shape time index - standardCircleBanach‖ ^ 2 := by
  rw [abs_mul]
  have estimate := mul_le_mul_of_nonneg_left
    (flow.domain_centered_radial_second_moment_deformation_bound inside index small)
    (abs_nonneg (configuration.density index))
  exact estimate.trans_eq (by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ Real.pi * configuration.radius index ^ 2 by positivity)]
    ring)

theorem domain_radial_moment_recenter (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (index : Fin count) (center : ℂ) :
    (∫ position in flow.domain time index, ‖position - center‖ ^ 2) =
      (∫ position in flow.domain time index, ‖position - flow.centroid time index‖ ^ 2) +
        (Real.pi * configuration.radius index ^ 2) * ‖flow.centroid time index - center‖ ^ 2 := by
  have squareIntegrable : IntegrableOn (fun position : ℂ => ‖position - flow.centroid time index‖ ^ 2)
      (flow.domain time index) :=
    (((continuous_id.sub continuous_const).norm.pow 2).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure
  have identity := integral_norm_sub_centroid_eq (flow.domain_identity_integrable time index) squareIntegrable
    (flow.domain_isBounded time index).measure_lt_top (center := center)
    (flow.domain_centroid_centered_integral inside index)
  have area : volume.real (flow.domain time index) = Real.pi * configuration.radius index ^ 2 :=
    flow.domain_area inside index
  rw [area] at identity
  linarith

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
