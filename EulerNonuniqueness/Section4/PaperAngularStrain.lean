import EulerNonuniqueness.Section6.PaperExternalMomentDynamics
import EulerNonuniqueness.Section6.PaperExternalStaticData
import EulerNonuniqueness.Section6.PaperExternalStrain
import EulerNonuniqueness.General.WeightedAngularStrain

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem FinitePatchEvolution.angularImpulse_strain_error_of_boundary_gaps
    {count : ℕ} {scales : Scales} {motion : PatchMotion count} {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales motion horizon) (horizonPositive : 0 < horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (patchRadiusPositive : ∀ index : Fin count, 0 < scales.radius (index.val + 1))
    (control : ∀ current ∈ Icc 0 horizon, ∀ index patch,
      ∃ bound ≤ (1 : ℝ), BoundaryCloseToCircle scales motion current index patch bound)
    (labelGaps : ∀ current ∈ Icc 0 horizon, ∀ (index other : Fin count) (patch otherPatch : Fin 4),
      (other, otherPatch) ≠ (index, patch) →
      8 * scales.radius (index.val + 1) + 8 * scales.radius (other.val + 1) <
        dist (motion.boundary current index patch 0) (motion.boundary current other otherPatch 0))
    (timeInside : time ∈ Ioo 0 horizon)
    (index : Fin count) (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, motion.domain time index patch ⊆ Metric.closedBall (quadrupoleCenter motion time index) radius)
    (distance : Fin count → ℝ) (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ motion.domain time source patch,
      distance source ≤ ‖quadrupoleCenter motion time index - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source) :
    |deriv (fun current => angularImpulse scales motion current index) time -
      2 * (Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index)
        (quadrupoleCenter motion time index) *
          star (∫ position, quadrupoleDensity scales motion time index position •
            (position - quadrupoleCenter motion time index) ^ 2)).re| ≤
      8 * scales.circulation (index.val + 1) * ‖centroidAsymmetry motion time index‖ *
        ‖biotSavart (externalPatchVorticity scales motion time index) (quadrupoleCenter motion time index) -
          deriv (fun current => quadrupoleCenter motion current index) time‖ +
      8 * scales.circulation (index.val + 1) * radius ^ 3 *
        ∑ source ∈ Finset.univ.erase index, 4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3) := by
  classical
  have closed : time ∈ Icc 0 horizon := ⟨timeInside.1.le, timeInside.2.le⟩
  let center := quadrupoleCenter motion time index
  let density := quadrupoleDensity scales motion time index
  let velocity := biotSavart (externalPatchVorticity scales motion time index)
  let coefficient := Section6.vorticityComplexStrain (externalPatchVorticity scales motion time index) center
  let hessian := ∑ source ∈ Finset.univ.erase index, 4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have hessianNonnegative : 0 ≤ hessian := Finset.sum_nonneg fun source member =>
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have velocityIdentity (position : ℂ) : velocity position =
      biotSavart (externalPatchVorticity scales motion time index) position := rfl
  have compact := evolution.externalPatchVorticity_compactSupport closed index
  obtain ⟨supportRadius, supportRadiusPositive, supportBound⟩ := compact.isCompact.isBounded.exists_pos_norm_le
  have supported : Function.support (externalPatchVorticity scales motion time index) ⊆ Metric.closedBall 0 supportRadius := by
    intro position member
    simpa only [Metric.mem_closedBall, dist_zero_right] using supportBound position (subset_tsupport _ member)
  have velocityContinuous : Continuous velocity :=
    continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
      (evolution.externalPatchVorticity_memLp closed index (ENNReal.ofReal (4 : ℝ))) (by norm_num)
      supportRadiusPositive.le supported
  have weightIntegrable {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
      (function : ℂ → Value) (continuous : Continuous function) :
      Integrable (fun position => density position • function position) := by
    simp only [density, quadrupoleDensity, Finset.sum_smul]
    exact integrable_finset_sum _ (fun patch _ =>
      evolution.integrable_patchDensity_smul_continuous closed index patch continuous)
  have massIntegrable : Integrable density := evolution.quadrupoleDensity_integrable closed index
  have firstIntegrable : Integrable (fun position => density position • (position - center)) :=
    weightIntegrable (Value := ℂ) (fun position : ℂ => position - center) (continuous_id.sub continuous_const)
  have complexMomentIntegrable : Integrable (fun position => density position • (position - center) ^ 2) :=
    weightIntegrable (Value := ℂ) (fun position : ℂ => (position - center) ^ 2) ((continuous_id.sub continuous_const).pow 2)
  have secondIntegrable : Integrable (fun position => |density position| * ‖position - center‖ ^ 2) := by
    have integrable := weightIntegrable (Value := ℝ) (fun position : ℂ => ‖position - center‖ ^ 2)
      ((continuous_id.sub continuous_const).norm.pow 2)
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using integrable.norm
  have supportBound (position : ℂ) (member : position ∈ Function.support density) : ‖position - center‖ ≤ radius := by
    by_contra failure
    have zero (patch : Fin 4) : patchDensity scales motion time index patch position = 0 := by
      apply indicator_of_not_mem
      intro patchMember
      exact failure (by simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded patch patchMember)
    exact member (by simp only [density, quadrupoleDensity, zero, Finset.sum_const_zero])
  have secondBound : (∫ position, |density position| * ‖position - center‖ ^ 2) ≤ 4 * scales.circulation (index.val + 1) * radius ^ 2 := by
    have estimate := integral_mono_ae secondIntegrable (massIntegrable.norm.const_mul (radius ^ 2))
      (Filter.Eventually.of_forall fun position => by
        by_cases zero : density position = 0
        · simp [zero]
        · exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (supportBound position zero) 2)
            (abs_nonneg _)).trans_eq (mul_comm _ _))
    rw [integral_const_mul] at estimate
    exact estimate.trans ((mul_le_mul_of_nonneg_left
      (evolution.quadrupoleDensity_integral_abs_le closed amplitudePositive frequencyPositive ratioPositive index)
      (sq_nonneg radius)).trans_eq (by ring))
  have remainder (position : ℂ) (member : position ∈ Function.support density) :
      ‖velocity position - velocity center - coefficient * star (position - center)‖ ≤ (hessian * radius) * ‖position - center‖ := by
    rw [velocityIdentity, velocityIdentity]
    have actualDerivative := evolution.externalPatch_biotSavart_hasFDerivAt_complexStrain closed index distance positive separated
    have estimate := evolution.externalPatch_biotSavart_fderiv_taylor_bound closed amplitudePositive frequencyPositive ratioPositive
      index distance positive separated (fun source different => (mul_le_mul_of_nonneg_left (supportBound position member) (by norm_num)).trans (near source different))
    rw [actualDerivative.fderiv] at estimate
    change ‖biotSavart (externalPatchVorticity scales motion time index) position -
      biotSavart (externalPatchVorticity scales motion time index) center - coefficient * star (position - center)‖ ≤
        hessian * ‖position - center‖ ^ 2 at estimate
    apply estimate.trans
    have product := mul_le_mul_of_nonneg_right (supportBound position member) (mul_nonneg hessianNonnegative (norm_nonneg (position - center)))
    nlinarith only [product]
  have fluxBound := integral_weighted_angular_strain_difference_le massIntegrable center
    (deriv (fun current => quadrupoleCenter motion current index) time) coefficient firstIntegrable secondIntegrable
    complexMomentIntegrable velocityContinuous (mul_nonneg hessianNonnegative radiusNonnegative) remainder
  rw [evolution.integral_quadrupoleDensity_first_moment closed amplitudePositive frequencyPositive ratioPositive index center,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)] at fluxBound
  have derivative := evolution.angularImpulse_hasDerivAt_external_of_boundary_gaps horizonPositive
    amplitudePositive frequencyPositive ratioPositive patchRadiusPositive control labelGaps index timeInside
  rw [derivative.deriv]
  have scaled := mul_le_mul_of_nonneg_left (fluxBound.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left secondBound (mul_nonneg hessianNonnegative radiusNonnegative)) _)) (by norm_num : (0 : ℝ) ≤ 2)
  have absoluteScale (first second : ℝ) : |2 * first - 2 * second| = 2 * |first - second| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [absoluteScale]
  dsimp only [center, density, coefficient, hessian] at scaled ⊢
  rw [velocityIdentity center] at scaled
  convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper
