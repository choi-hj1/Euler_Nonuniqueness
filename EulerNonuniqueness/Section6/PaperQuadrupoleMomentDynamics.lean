import EulerNonuniqueness.Section6.PaperCentroidMomentDynamics
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

theorem FinitePatchEvolution.quadrupole_smooth_moment_hasDerivAt_of_boundary_gaps
    (index : Fin count) {test : ℂ → ℝ} (smooth : ContDiff ℝ ∞ test) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, quadrupoleDensity scales motion current index position * test position)
      (∫ position, quadrupoleDensity scales motion time index position *
        fderiv ℝ test position (biotSavart (patchVorticity scales motion time) position)) time := by
  have integralIdentity (current : ℝ) (member : current ∈ Icc 0 horizon) {function : ℂ → ℝ} (continuous : Continuous function) :
      (∫ position, quadrupoleDensity scales motion current index position * function position) =
        ∑ patch : Fin 4, ∫ position, patchDensity scales motion current index patch position * function position := by
    simp only [quadrupoleDensity, Finset.sum_mul]
    rw [integral_finset_sum _ (fun patch _ => by
      simpa only [smul_eq_mul] using evolution.integrable_patchDensity_smul_continuous member index patch continuous)]
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have fluxContinuous := (smooth.continuous_fderiv (by simp)).clm_apply
    (analytic.continuous_biotSavart ⟨inside.1.le, inside.2.le⟩)
  have actual := HasDerivAt.sum (u := Finset.univ) fun patch _ =>
    evolution.hasDerivAt_patch_supported_smooth_moment_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
      radiusPositive control separated index patch smooth inside
  rw [← integralIdentity time ⟨inside.1.le, inside.2.le⟩ fluxContinuous] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  exact integralIdentity current ⟨member.1.le, member.2.le⟩ smooth.continuous

theorem FinitePatchEvolution.quadrupole_first_moment_hasDerivAt_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, quadrupoleDensity scales motion current index position • position)
      (∫ position, quadrupoleDensity scales motion time index position •
        biotSavart (patchVorticity scales motion time) position) time := by
  have integralIdentity (current : ℝ) (member : current ∈ Icc 0 horizon) {function : ℂ → ℂ} (continuous : Continuous function) :
      (∫ position, quadrupoleDensity scales motion current index position • function position) =
        ∑ patch : Fin 4, ∫ position, patchDensity scales motion current index patch position • function position := by
    simp only [quadrupoleDensity, Finset.sum_smul]
    rw [integral_finset_sum _ (fun patch _ => evolution.integrable_patchDensity_smul_continuous member index patch continuous)]
  have analytic := evolution.transportAnalyticHypotheses_of_boundary_control amplitudePositive frequencyPositive ratioPositive radiusPositive control
  have actual := HasDerivAt.sum (u := Finset.univ) fun patch _ =>
    evolution.hasDerivAt_patch_complex_first_moment_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
      radiusPositive control separated index patch inside
  rw [← integralIdentity time ⟨inside.1.le, inside.2.le⟩
    (analytic.continuous_biotSavart ⟨inside.1.le, inside.2.le⟩)] at actual
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  exact integralIdentity current ⟨member.1.le, member.2.le⟩ continuous_id

theorem FinitePatchEvolution.centroidAsymmetry_hasDerivAt_of_boundary_gaps
    (index : Fin count) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => centroidAsymmetry motion current index)
      ((4 * scales.circulation (index.val + 1))⁻¹ • ∫ position,
        quadrupoleDensity scales motion time index position • biotSavart (patchVorticity scales motion time) position) time := by
  have circulationPositive := scales.circulation_pos frequencyPositive ratioPositive (index.val + 1)
  have actual := (evolution.quadrupole_first_moment_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index inside).const_smul (4 * scales.circulation (index.val + 1))⁻¹
  apply actual.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds inside] with current member
  have identity := evolution.integral_quadrupoleDensity_first_moment ⟨member.1.le, member.2.le⟩ amplitudePositive frequencyPositive ratioPositive index 0
  simp only [sub_zero] at identity
  rw [identity, smul_smul, inv_mul_cancel₀ (by positivity : 4 * scales.circulation (index.val + 1) ≠ 0), one_smul]

theorem FinitePatchEvolution.quadrupole_fixed_angular_moment_hasDerivAt_of_boundary_gaps
    (index : Fin count) (center : ℂ) (inside : time ∈ Ioo 0 horizon) :
    HasDerivAt (fun current => ∫ position, quadrupoleDensity scales motion current index position * ‖position - center‖ ^ 2)
      (2 * ∫ position, @inner ℝ ℂ _ (position - center)
        (quadrupoleDensity scales motion time index position • biotSavart (patchVorticity scales motion time) position)) time := by
  have smooth : ContDiff ℝ ∞ (fun position : ℂ => ‖position - center‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have differential (position : ℂ) : fderiv ℝ (fun other : ℂ => ‖other - center‖ ^ 2) position =
      (2 : ℝ) • innerSL ℝ (position - center) := by
    simpa only [ContinuousLinearMap.comp_id, id_eq, two_smul] using
      (((hasFDerivAt_id position).sub_const center).norm_sq).fderiv
  have actual := evolution.quadrupole_smooth_moment_hasDerivAt_of_boundary_gaps horizonPositive amplitudePositive frequencyPositive ratioPositive
    radiusPositive control separated index smooth inside
  simp only [differential, ContinuousLinearMap.smul_apply, innerSL_apply, smul_eq_mul] at actual
  convert actual using 1
  rw [← integral_const_mul]
  congr 1
  funext position
  rw [real_inner_smul_right]
  ring

end EulerNonuniqueness.Paper
