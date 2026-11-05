import EulerNonuniqueness.Section6.FinitePatchSubfamilyMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteLiteralPatchFlow

variable {count : ℕ} {configuration : FiniteContourConfiguration count}

theorem subfamily_first_moment_hasDerivAt_external (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position • position)
      (∫ position, flow.subfamilyVorticity selected time position •
        (biotSavart (flow.vorticity time) position -
          biotSavart (flow.subfamilyVorticity selected time) position)) time := by
  have fullIntegrable := flow.integrable_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => flow.domain_velocity_integrable time index)
  have ownIntegrable := Section6.integrable_vorticity_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time)
  simp_rw [smul_sub]
  rw [integral_sub fullIntegrable ownIntegrable, flow.subfamily_internal_first_moment_zero, sub_zero]
  exact flow.subfamily_first_moment_hasDerivAt selected inside

theorem subfamily_angular_velocity_integrable (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) (time : ℝ) (center : ℂ) :
    Integrable (fun position => @inner ℝ ℂ _ (position - center)
      (flow.subfamilyVorticity selected time position • biotSavart (flow.vorticity time) position)) := by
  simp_rw [real_inner_smul_right]
  exact flow.integrable_subfamilyVorticity_smul selected time _ fun index _ =>
    (((continuous_id.sub continuous_const).inner (flow.biotSavart_continuous time)).continuousOn.integrableOn_compact
      (flow.domain_isBounded time index).isCompact_closure).mono_set subset_closure

theorem subfamily_angular_moment_hasDerivAt_external (flow : FiniteLiteralPatchFlow configuration)
    (selected : Finset (Fin count)) {time : ℝ} (inside : time ∈ Ioo (-flow.duration) flow.duration)
    (center : ℂ) :
    HasDerivAt (fun parameter => ∫ position,
      flow.subfamilyVorticity selected parameter position * ‖position - center‖ ^ 2)
      (2 * ∫ position, @inner ℝ ℂ _ (position - center)
        (flow.subfamilyVorticity selected time position •
          (biotSavart (flow.vorticity time) position -
            biotSavart (flow.subfamilyVorticity selected time) position))) time := by
  have ownIntegrable := Section6.integrable_vorticity_angular_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time) center
  simp_rw [smul_sub, inner_sub_right]
  rw [integral_sub (flow.subfamily_angular_velocity_integrable selected time center) ownIntegrable,
    flow.subfamily_internal_angular_moment_zero, sub_zero]
  have derivative := flow.subfamily_angular_moment_hasDerivAt selected inside center
  convert derivative using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [real_inner_smul_right]
    ring

end EulerNonuniqueness.Paper.FiniteLiteralPatchFlow
