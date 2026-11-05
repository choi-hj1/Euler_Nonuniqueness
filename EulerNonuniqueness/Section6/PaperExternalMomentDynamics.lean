import EulerNonuniqueness.Section6.PaperAngularMomentDynamics
import EulerNonuniqueness.Section6.PaperQuadrupoleSelfCancellation
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

private theorem external_velocity_identity (index : Fin count) {current : ℝ} (member : current ∈ Icc 0 horizon) (position : ℂ) :
    biotSavart (patchVorticity scales motion current) position -
      biotSavart (quadrupoleDensity scales motion current index) position =
        biotSavart (externalPatchVorticity scales motion current index) position := by
  have actual := evolution.patchVorticity_biotSavart_internal_external member index position
  rw [← evolution.quadrupole_biotSavart_eq_sum_patch member index position] at actual
  rw [actual]
  abel

private theorem external_quad_weight_integrable {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {current : ℝ} (member : current ∈ Icc 0 horizon) (index : Fin count) {function : ℂ → Value} (continuous : Continuous function) :
    Integrable (fun position => quadrupoleDensity scales motion current index position • function position) := by
  simp only [quadrupoleDensity, Finset.sum_smul]
  exact integrable_finset_sum _ fun patch _ => evolution.integrable_patchDensity_smul_continuous member index patch continuous

theorem FinitePatchEvolution.quadrupole_first_moment_hasDerivAt_external_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, quadrupoleDensity scales motion current index position • position)
      (∫ position, quadrupoleDensity scales motion time index position •
        biotSavart (externalPatchVorticity scales motion time index) position) time := by
  have closed : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have fullIntegrable := external_quad_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
    closed index (analytic.continuous_biotSavart closed)
  have cancellation := evolution.quadrupole_self_cancellation_genuine closed index 0
  have identity : (∫ position, quadrupoleDensity scales motion time index position •
      biotSavart (externalPatchVorticity scales motion time index) position) =
      ∫ position, quadrupoleDensity scales motion time index position • biotSavart (patchVorticity scales motion time) position := by
    simp_rw [← external_velocity_identity evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index closed, smul_sub]
    rw [integral_sub fullIntegrable cancellation.1, cancellation.2.1, sub_zero]
  rw [identity]
  exact evolution.quadrupole_first_moment_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside

theorem FinitePatchEvolution.centroidAsymmetry_hasDerivAt_external_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => centroidAsymmetry motion current index)
      ((4 * scales.circulation (index.val + 1))⁻¹ • ∫ position,
        quadrupoleDensity scales motion time index position • biotSavart (externalPatchVorticity scales motion time index) position) time := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have actual := (evolution.quadrupole_first_moment_hasDerivAt_external_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside).const_smul (4 * scales.circulation (index.val + 1))⁻¹
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  have identity := evolution.integral_quadrupoleDensity_first_moment ⟨member.1.le, member.2.le⟩ amplitudePositive frequencyPositive ratioPositive index 0
  simp only [sub_zero] at identity
  rw [identity, smul_smul, inv_mul_cancel₀ (by positivity : 4 * scales.circulation (index.val + 1) ≠ 0), one_smul]

theorem FinitePatchEvolution.angularImpulse_hasDerivAt_external_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => angularImpulse scales motion current index)
      (2 * ∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter motion time index)
        (quadrupoleDensity scales motion time index position •
          (biotSavart (externalPatchVorticity scales motion time index) position -
            deriv (fun current => quadrupoleCenter motion current index) time))) time := by
  have closed : time ∈ Icc 0 horizon := ⟨inside.1.le, inside.2.le⟩
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have fullIntegrable : Integrable (fun position => @inner ℝ ℂ _ (position - quadrupoleCenter motion time index)
      (quadrupoleDensity scales motion time index position •
        (biotSavart (patchVorticity scales motion time) position - deriv (fun current => quadrupoleCenter motion current index) time))) := by
    simpa only [real_inner_smul_right, smul_eq_mul] using
      external_quad_weight_integrable evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated
        closed index ((continuous_id.sub continuous_const).inner ((analytic.continuous_biotSavart closed).sub continuous_const))
  have cancellation := evolution.quadrupole_self_cancellation_genuine closed index (quadrupoleCenter motion time index)
  have identity :
      (∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter motion time index)
        (quadrupoleDensity scales motion time index position •
          (biotSavart (externalPatchVorticity scales motion time index) position -
            deriv (fun current => quadrupoleCenter motion current index) time))) =
      ∫ position, @inner ℝ ℂ _ (position - quadrupoleCenter motion time index)
        (quadrupoleDensity scales motion time index position •
          (biotSavart (patchVorticity scales motion time) position -
            deriv (fun current => quadrupoleCenter motion current index) time)) := by
    simp_rw [← external_velocity_identity evolution horizonPositive amplitudePositive frequencyPositive ratioPositive radiusPositive control separated index closed]
    have rearrange (position : ℂ) :
        biotSavart (patchVorticity scales motion time) position - biotSavart (quadrupoleDensity scales motion time index) position -
            deriv (fun current => quadrupoleCenter motion current index) time =
        (biotSavart (patchVorticity scales motion time) position - deriv (fun current => quadrupoleCenter motion current index) time) -
          biotSavart (quadrupoleDensity scales motion time index) position := by abel
    simp_rw [rearrange, smul_sub, inner_sub_right]
    have fullExpanded := fullIntegrable
    simp only [smul_sub, inner_sub_right] at fullExpanded
    rw [integral_sub fullExpanded cancellation.2.2.1, cancellation.2.2.2, sub_zero]
  rw [identity]
  exact evolution.angularImpulse_hasDerivAt_flux_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside

end EulerNonuniqueness.Paper

