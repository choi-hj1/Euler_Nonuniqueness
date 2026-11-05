import EulerNonuniqueness.Section6.PatchCentroidQuadraticMoment
import EulerNonuniqueness.Section6.FinitePatchSubfamilyMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

set_option synthInstance.maxHeartbeats 100000

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem subfamily_complex_second_moment_integral_hasDerivAt (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) (selected : Finset (Fin count)) :
    HasDerivAt (fun parameter => ∫ position,
        flow.subfamilyVorticity selected parameter position • position ^ 2)
      (∫ position, flow.subfamilyVorticity selected time position •
        (2 * position * biotSavart (flow.vorticity time) position)) time := by
  have momentIdentity (parameter : ℝ) :
      (∫ position, flow.subfamilyVorticity selected parameter position • position ^ 2) =
        ∑ index ∈ selected, configuration.density index •
          (∫ position in flow.domain parameter index, position ^ 2) := by
    exact flow.integral_subfamilyVorticity_smul selected parameter _ fun index _ =>
      (((continuous_id.pow 2).continuousOn.integrableOn_compact
        (flow.domain_isBounded parameter index).isCompact_closure).mono_set subset_closure)
  have rateIdentity :
      (∫ position, flow.subfamilyVorticity selected time position •
        (2 * position * biotSavart (flow.vorticity time) position)) =
      ∑ index ∈ selected, configuration.density index •
        (∫ position in flow.domain time index, 2 * position * biotSavart (flow.vorticity time) position) := by
    exact flow.integral_subfamilyVorticity_smul selected time _ fun index _ =>
      ((((continuous_const.mul continuous_id).mul (flow.biotSavart_continuous time)).continuousOn.integrableOn_compact
        (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure)
  simp_rw [momentIdentity]
  rw [rateIdentity]
  exact flow.subfamily_complex_second_moment_hasDerivAt inside selected

theorem subfamily_complex_second_moment_integral_point_error (flow : FiniteLiteralPatchFlow configuration)
    {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (selected : Finset (Fin count)) (reference : ℂ)
    (small : ∀ index ∈ selected, ‖flow.shape time index - standardCircleBanach‖ ≤ 1 / 16) :
    ‖(∫ position, flow.subfamilyVorticity selected time position • (position - reference) ^ 2) -
      ∑ index ∈ selected, (configuration.density index * (Real.pi * configuration.radius index ^ 2)) •
        (flow.centroid time index - reference) ^ 2‖ ≤
      ∑ index ∈ selected, 128 * |configuration.density index * (Real.pi * configuration.radius index ^ 2)| *
        configuration.radius index ^ 2 * ‖flow.shape time index - standardCircleBanach‖ := by
  rw [flow.integral_subfamilyVorticity_smul selected time
    (fun position : ℂ => (position - reference) ^ 2) (fun index _ =>
    ((((continuous_id.sub continuous_const).pow 2).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure))]
  exact flow.subfamily_complex_second_moment_point_error inside selected reference small

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
