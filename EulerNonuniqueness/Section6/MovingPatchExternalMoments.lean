import EulerNonuniqueness.Section6.MovingPatchSubfamilyMoments

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem subfamily_first_moment_hasDerivAt_external (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label)) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position • position)
      (∫ position, flow.subfamilyVorticity selected time position •
        (biotSavart (flow.vorticity time) position -
          biotSavart (flow.subfamilyVorticity selected time) position)) time := by
  have fullIntegrable := flow.integrable_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => (flow.patch index).integral_continuous_function time (flow.biotSavart_continuous time))
  have ownIntegrable := Section6.integrable_vorticity_self_interaction
    (flow.subfamilyVorticity_integrable selected time) (flow.subfamilyVorticity_support selected time)
    (flow.abs_subfamilyVorticity_le selected time)
  simp_rw [smul_sub]
  rw [integral_sub fullIntegrable ownIntegrable, flow.subfamily_internal_first_moment_zero, sub_zero]
  exact flow.subfamily_first_moment_hasDerivAt selected inside material

theorem subfamily_angular_velocity_integrable (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) (time : ℝ) (center : ℂ) :
    Integrable (fun position => @inner ℝ ℂ _ (position - center)
      (flow.subfamilyVorticity selected time position • biotSavart (flow.vorticity time) position)) := by
  simp_rw [real_inner_smul_right]
  exact flow.integrable_subfamilyVorticity_smul selected time _ fun index _ =>
    (((continuous_id.sub continuous_const).inner (flow.biotSavart_continuous time)).continuousOn.integrableOn_compact
      ((flow.patch index).domain_isBounded time).isCompact_closure).mono_set subset_closure

theorem subfamily_angular_moment_hasDerivAt_external (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label))
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
  have derivative := flow.subfamily_angular_moment_hasDerivAt selected inside material center
  convert derivative using 1
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun position => by
    dsimp only
    rw [real_inner_smul_right]
    ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
