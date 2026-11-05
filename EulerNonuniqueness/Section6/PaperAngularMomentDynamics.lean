import EulerNonuniqueness.Section6.PaperQuadrupoleMomentDynamics
import EulerNonuniqueness.General.WeightedAngularFlux
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000

variable {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time : ℝ}
variable (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
variable (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
variable (radiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
variable (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
  ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
variable (separated : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
  (other, otherPatch) ≠ (index, patch) → 8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
    dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))

include evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated

private theorem quad_continuous_weight_integrable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {current : ℝ} (member : current ∈ Icc 0 horizon) (index : Fin count) {function : ℂ → Value} (continuous : Continuous function) :
    Integrable (fun position => quadrupoleDensity scales motion current index position • function position) := by
  simp only [quadrupoleDensity, Finset.sum_smul]
  exact integrable_finset_sum _ fun patch _ => evolution.integrable_patchDensity_smul_continuous member index patch continuous

theorem FinitePatchEvolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => quadrupoleCenter motion current index)
      ((∑ patch : Fin 4, patchAverageVelocity scales motion time index patch
        (biotSavart (patchVorticity scales motion time))) / 4) time := by
  exact (HasDerivAt.sum (u := Finset.univ) fun patch _ =>
    evolution.patchCentroid_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
      radiusPositive control separated index patch inside).div_const 4

theorem FinitePatchEvolution.angularImpulse_hasDerivAt_flux_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => angularImpulse scales motion current index)
      (2 * ∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter motion time index)
        (quadrupoleDensity scales motion time index position •
          (biotSavart (patchVorticity scales motion time) position -
            deriv (fun current => quadrupoleCenter motion current index) time))) time := by
  have closed : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have velocityContinuous := analytic.continuous_biotSavart closed
  have massIntegrable (current : ℝ) (member : current ∈ Icc 0 horizon) :=
    evolution.quadrupoleDensity_integrable member index
  have firstIntegrable (current : ℝ) (member : current ∈ Icc 0 horizon) :=
    quad_continuous_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
      member index continuous_id
  have secondIntegrable (current : ℝ) (member : current ∈ Icc 0 horizon) :
      Integrable (fun position => quadrupoleDensity scales motion current index position * ‖position‖ ^ 2) := by
    simpa only [smul_eq_mul] using
      quad_continuous_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
        member index (continuous_norm.pow 2)
  have velocityIntegrable :=
    quad_continuous_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
      closed index velocityContinuous
  have angularIntegrable : Integrable (fun position => @inner ℝ ℂ _ position
      (quadrupoleDensity scales motion time index position • biotSavart (patchVorticity scales motion time) position)) := by
    simpa only [real_inner_smul_right, smul_eq_mul] using
      quad_continuous_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
        closed index (continuous_id.inner velocityContinuous)
  have zeroMass (current : ℝ) (member : current ∈ Icc 0 horizon) :
      (∫ position, quadrupoleDensity scales motion current index position) = 0 := by
    have properties := evolution.2.2.2.1 current member index
    exact quadrupoleDensity_integral_zero scales motion current index (fun patch => (properties patch).1)
      (fun patch => (properties patch).2.1) (fun patch => (properties patch).2.2.1)
      amplitudePositive frequencyPositive ratioPositive
  have identity (current : ℝ) (member : current ∈ Icc 0 horizon) :
      angularImpulse scales motion current index =
        (∫ position, quadrupoleDensity scales motion current index position * ‖position‖ ^ 2) -
          2 * @inner ℝ ℂ _ (quadrupoleCenter motion current index)
            (∫ position, quadrupoleDensity scales motion current index position • position) := by
    have expansion := integral_weighted_norm_sub_sq (massIntegrable current member) (firstIntegrable current member)
      (secondIntegrable current member) (quadrupoleCenter motion current index)
    rw [zeroMass current member, mul_zero, add_zero] at expansion
    convert expansion using 1
    unfold angularImpulse
    apply integral_congr_ae
    exact Eventually.of_forall fun position => mul_comm _ _
  have firstEquation := evolution.quadrupole_first_moment_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside
  have secondEquation := evolution.quadrupole_fixed_angular_moment_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index 0 inside
  simp only [sub_zero] at secondEquation
  have centerEquation := (evolution.quadrupoleCenter_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside).differentiableAt.hasDerivAt
  have raw := secondEquation.sub ((centerEquation.inner ℝ firstEquation).const_mul 2)
  have agreement :
      (fun current => angularImpulse scales motion current index) =ᶠ[𝓝 time]
        (fun current => (∫ position, quadrupoleDensity scales motion current index position * ‖position‖ ^ 2) -
          2 * @inner ℝ ℂ _ (quadrupoleCenter motion current index)
            (∫ position, quadrupoleDensity scales motion current index position • position)) := by
    filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
    exact identity current ⟨member.1.le, member.2.le⟩
  have actual := raw.congr_of_eventuallyEq agreement
  have flux := integral_weighted_angular_flux (massIntegrable time closed) (firstIntegrable time closed)
    velocityIntegrable angularIntegrable (quadrupoleCenter motion time index)
    (deriv (fun current => quadrupoleCenter motion current index) time)
  rw [zeroMass time closed, mul_zero, add_zero] at flux
  convert actual using 1
  rw [flux]
  ring

end EulerNonuniqueness.Paper

