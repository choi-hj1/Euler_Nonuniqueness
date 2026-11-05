import EulerNonuniqueness.Section6.MovingPatchExternalMoments
import EulerNonuniqueness.General.WeightedAngularFlux

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

variable {count : ℕ}

theorem subfamily_continuous_weight_integrable {value : Type*}
    [NormedAddCommGroup value] [NormedSpace ℝ value]
    (flow : FiniteMovingPatchFamily count) (selected : Finset (Fin count))
    (time : ℝ) (function : ℂ → value) (continuous : Continuous function) :
    Integrable (fun position => flow.subfamilyVorticity selected time position • function position) := by
  exact flow.integrable_subfamilyVorticity_smul selected time function fun index _ =>
    (continuous.continuousOn.integrableOn_compact
      ((flow.patch index).domain_isBounded time).isCompact_closure).mono_set subset_closure

theorem subfamily_mass_hasDerivAt (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label)) :
    HasDerivAt (fun parameter => ∫ position, flow.subfamilyVorticity selected parameter position) 0 time := by
  have derivative := flow.subfamily_integral_hasDerivAt selected inside material (fun _ => (1 : ℝ))
    (fun _ => (0 : ℂ →L[ℝ] ℝ)) continuous_const continuous_const
    (fun position => hasFDerivAt_const (1 : ℝ) position)
  simpa only [mul_one, ContinuousLinearMap.zero_apply, mul_zero, integral_zero] using derivative

theorem subfamily_moving_angular_moment_hasDerivAt (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label))
    {center : ℝ → ℂ} {centerDerivative : ℂ} (centerEquation : HasDerivAt center centerDerivative time) :
    HasDerivAt (fun parameter => ∫ position,
      flow.subfamilyVorticity selected parameter position * ‖position - center parameter‖ ^ 2)
      (2 * ∫ position, @inner ℝ ℂ _ (position - center time)
        (flow.subfamilyVorticity selected time position •
          (biotSavart (flow.vorticity time) position - centerDerivative))) time := by
  have massIntegrable := flow.subfamilyVorticity_integrable selected
  have firstIntegrable := fun parameter => flow.subfamily_continuous_weight_integrable selected parameter id continuous_id
  have secondIntegrable := fun parameter => flow.subfamily_continuous_weight_integrable selected parameter
    (fun position => ‖position‖ ^ 2) (continuous_norm.pow 2)
  have fullIntegrable := flow.integrable_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => (flow.patch index).integral_continuous_function time (flow.biotSavart_continuous time))
  have angularIntegrable : Integrable (fun position => @inner ℝ ℂ _ position
      (flow.subfamilyVorticity selected time position • biotSavart (flow.vorticity time) position)) := by
    simpa only [sub_zero] using flow.subfamily_angular_velocity_integrable selected time 0
  have rawDerivative := flow.subfamily_angular_moment_hasDerivAt selected inside material 0
  simp only [sub_zero] at rawDerivative
  have rawRateIdentity :
      (∫ position, flow.subfamilyVorticity selected time position *
        (2 * @inner ℝ ℂ _ position (biotSavart (flow.vorticity time) position))) =
      2 * ∫ position, @inner ℝ ℂ _ position
        (flow.subfamilyVorticity selected time position • biotSavart (flow.vorticity time) position) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun position => by
      dsimp only
      rw [real_inner_smul_right]
      ring
  rw [rawRateIdentity] at rawDerivative
  have derivative := hasDerivAt_weighted_angular_moment massIntegrable firstIntegrable secondIntegrable
    (flow.subfamily_mass_hasDerivAt selected inside material) (flow.subfamily_first_moment_hasDerivAt selected inside material)
    rawDerivative centerEquation
  have fluxIdentity := integral_weighted_angular_flux (massIntegrable time) (firstIntegrable time)
    fullIntegrable angularIntegrable (center time) centerDerivative
  convert derivative using 1
  rw [fluxIdentity]
  ring

theorem subfamily_moving_angular_moment_hasDerivAt_external (flow : FiniteMovingPatchFamily count)
    (selected : Finset (Fin count)) {time : ℝ} (inside : ∀ index, time ∈ Ioo (flow.patch index).initialTime (flow.patch index).finalTime)
    (material : ∀ index label, (flow.patch index).boundaryVelocity time label =
      biotSavart (flow.vorticity time) ((flow.patch index).boundary time label))
    {center : ℝ → ℂ} {centerDerivative : ℂ} (centerEquation : HasDerivAt center centerDerivative time) :
    HasDerivAt (fun parameter => ∫ position,
      flow.subfamilyVorticity selected parameter position * ‖position - center parameter‖ ^ 2)
      (2 * ∫ position, @inner ℝ ℂ _ (position - center time)
        (flow.subfamilyVorticity selected time position •
          (biotSavart (flow.vorticity time) position -
            biotSavart (flow.subfamilyVorticity selected time) position - centerDerivative))) time := by
  have massIntegrable := flow.subfamilyVorticity_integrable selected time
  have firstIntegrable := flow.subfamily_continuous_weight_integrable selected time id continuous_id
  have fullIntegrable := flow.integrable_subfamilyVorticity_smul selected time
    (biotSavart (flow.vorticity time)) (fun index _ => (flow.patch index).integral_continuous_function time (flow.biotSavart_continuous time))
  have angularIntegrable : Integrable (fun position => @inner ℝ ℂ _ position
      (flow.subfamilyVorticity selected time position • biotSavart (flow.vorticity time) position)) := by
    simpa only [sub_zero] using flow.subfamily_angular_velocity_integrable selected time 0
  have movingIntegrable := integrable_weighted_angular_flux massIntegrable firstIntegrable
    fullIntegrable angularIntegrable (center time) centerDerivative
  have ownIntegrable := Section6.integrable_vorticity_angular_self_interaction massIntegrable
    (flow.subfamilyVorticity_support selected time) (flow.abs_subfamilyVorticity_le selected time) (center time)
  have identity :
      (∫ position, @inner ℝ ℂ _ (position - center time)
        (flow.subfamilyVorticity selected time position •
          (biotSavart (flow.vorticity time) position -
            biotSavart (flow.subfamilyVorticity selected time) position - centerDerivative))) =
      ∫ position, @inner ℝ ℂ _ (position - center time)
        (flow.subfamilyVorticity selected time position •
          (biotSavart (flow.vorticity time) position - centerDerivative)) := by
    have integrandIdentity (position : ℂ) :
        @inner ℝ ℂ _ (position - center time)
          (flow.subfamilyVorticity selected time position •
            (biotSavart (flow.vorticity time) position -
              biotSavart (flow.subfamilyVorticity selected time) position - centerDerivative)) =
        @inner ℝ ℂ _ (position - center time)
          (flow.subfamilyVorticity selected time position •
            (biotSavart (flow.vorticity time) position - centerDerivative)) -
        @inner ℝ ℂ _ (position - center time)
          (flow.subfamilyVorticity selected time position •
            biotSavart (flow.subfamilyVorticity selected time) position) := by
      simp only [smul_sub, inner_sub_right]
      ring
    simp_rw [integrandIdentity]
    rw [integral_sub movingIntegrable ownIntegrable, flow.subfamily_internal_angular_moment_zero, sub_zero]
  rw [identity]
  exact flow.subfamily_moving_angular_moment_hasDerivAt selected inside material centerEquation

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
