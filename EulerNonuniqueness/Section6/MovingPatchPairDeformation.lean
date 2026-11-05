import EulerNonuniqueness.Section6.ActualExternalResidualBounds

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem external_pair_deformation_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (receiver source : Fin count)
    (densityNonzero : configuration.density receiver ≠ 0) (receiverCenter sourceCenter : ℂ)
    {receiverDeformation sourceDeformation : ℝ}
    (receiverNonnegative : 0 ≤ receiverDeformation) (sourceNonnegative : 0 ≤ sourceDeformation)
    (receiverSmall : receiverDeformation ≤ 1 / 16) (sourceSmall : sourceDeformation ≤ 1 / 16)
    (receiverLower : Metric.ball receiverCenter (configuration.radius receiver * (1 - receiverDeformation)) ⊆ flow.domain time receiver)
    (receiverUpper : flow.domain time receiver ⊆ Metric.ball receiverCenter (configuration.radius receiver * (1 + receiverDeformation)))
    (sourceLower : Metric.ball sourceCenter (configuration.radius source * (1 - sourceDeformation)) ⊆ flow.domain time source)
    (sourceUpper : flow.domain time source ⊆ Metric.ball sourceCenter (configuration.radius source * (1 + sourceDeformation)))
    (receiverSeparated : 8 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖)
    (sourceSeparated : 4 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖(Real.pi * configuration.radius receiver ^ 2)⁻¹ •
        (∫ position in flow.domain time receiver, biotSavart (flow.componentVorticity time source) position) -
      (configuration.density source * (Real.pi * configuration.radius source ^ 2)) •
        biotSavartKernel (flow.centroid time receiver - flow.centroid time source)‖ ≤
      128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
        (configuration.radius source ^ 2 * sourceDeformation +
          8 * configuration.radius receiver ^ 2 * receiverDeformation) /
        (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  have sourceGeometry := Section6.patch_actual_centroid_geometry (flow.domain_isOpen time source).measurableSet
    sourceCenter (flow.centroid time source) (configuration.radius_pos source) sourceNonnegative sourceSmall
    sourceLower sourceUpper (flow.domain_area inside source) (flow.domain_centroid_centered_integral inside source)
  have receiverError := flow.component_actual_receiver_averaging_bound_of_trapping inside receiver source densityNonzero
    receiverCenter receiverNonnegative receiverSmall receiverLower receiverUpper sourceGeometry.2.1 receiverSeparated sourceSeparated
  have sourceError := Section6.biotSavart_patch_relative_deformation_bound
    (flow.domain_isOpen time source).measurableSet sourceCenter (flow.centroid time source) (flow.centroid time receiver)
    (configuration.radius_pos source) sourceNonnegative sourceSmall sourceLower sourceUpper
    (flow.domain_area inside source) (flow.domain_centroid_centered_integral inside source) sourceSeparated
    (configuration.density source)
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (biotSavart (flow.componentVorticity time source) (flow.centroid time receiver)) _).trans
  apply (add_le_add receiverError sourceError).trans_eq
  ring

theorem subfamilyInternalDeformationResidual_bound_of_trapping (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (receiver : Fin count) (member : receiver ∈ selected) (densityNonzero : configuration.density receiver ≠ 0)
    (centers : Fin count → ℂ) (deformation : Fin count → ℝ)
    (nonnegative : ∀ index ∈ selected, 0 ≤ deformation index)
    (small : ∀ index ∈ selected, deformation index ≤ 1 / 16)
    (lower : ∀ index ∈ selected, Metric.ball (centers index)
      (configuration.radius index * (1 - deformation index)) ⊆ flow.domain time index)
    (upper : ∀ index ∈ selected, flow.domain time index ⊆ Metric.ball (centers index)
      (configuration.radius index * (1 + deformation index)))
    (separated : ∀ source ∈ selected.erase receiver,
      8 * configuration.radius receiver ≤ ‖flow.centroid time receiver - flow.centroid time source‖ ∧
      4 * configuration.radius source ≤ ‖flow.centroid time receiver - flow.centroid time source‖) :
    ‖flow.subfamilyInternalDeformationResidual selected time receiver‖ ≤
      ∑ source ∈ selected.erase receiver,
        128 * |configuration.density source * (Real.pi * configuration.radius source ^ 2)| *
          (configuration.radius source ^ 2 * deformation source +
            8 * configuration.radius receiver ^ 2 * deformation receiver) /
          (Real.pi * ‖flow.centroid time receiver - flow.centroid time source‖ ^ 3) := by
  unfold subfamilyInternalDeformationResidual
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro source sourceMember
  have sourceInside := (Finset.mem_erase.mp sourceMember).2
  exact flow.external_pair_deformation_of_trapping inside receiver source densityNonzero (centers receiver) (centers source)
    (nonnegative receiver member) (nonnegative source sourceInside) (small receiver member) (small source sourceInside)
    (lower receiver member) (upper receiver member) (lower source sourceInside) (upper source sourceInside)
    (separated source sourceMember).1 (separated source sourceMember).2

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
