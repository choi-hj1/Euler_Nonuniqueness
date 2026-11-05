import EulerNonuniqueness.Section4.ReferenceAngularFlux
import EulerNonuniqueness.Section6.PaperExternalStrain
import EulerNonuniqueness.General.WeightedAngularStrain

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

theorem quadrupole_angularImpulse_strain_error_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4), family.density (finProdFinEquiv (index, patch)) =
      patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time radius : ℝ}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency) (ratioPositive : 0 < scales.ratio)
    (inside : ∀ source, time ∈ Ioo (family.patch source).initialTime (family.patch source).finalTime)
    (material : ∀ source label, (family.patch source).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch source).boundary time label))
    (index : Fin count) (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, family.patchMotion.domain time index patch ⊆ Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius)
    (distance : Fin count → ℝ) (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ source ∈ Finset.univ.erase index, ∀ patch, ∀ location ∈ family.patchMotion.domain time source patch,
      distance source ≤ ‖quadrupoleCenter family.patchMotion time index - location‖)
    (near : ∀ source ∈ Finset.univ.erase index, 2 * radius ≤ distance source) :
    |deriv (fun current => angularImpulse scales family.patchMotion current index) time -
      2 * (Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index)
        (quadrupoleCenter family.patchMotion time index) *
          star (∫ position, quadrupoleDensity scales family.patchMotion time index position •
            (position - quadrupoleCenter family.patchMotion time index) ^ 2)).re| ≤
      8 * scales.circulation (index.val + 1) * ‖centroidAsymmetry family.patchMotion time index‖ *
        ‖biotSavart (externalPatchVorticity scales family.patchMotion time index) (quadrupoleCenter family.patchMotion time index) -
          deriv (fun current => quadrupoleCenter family.patchMotion current index) time‖ +
      8 * scales.circulation (index.val + 1) * radius ^ 3 *
        ∑ source ∈ Finset.univ.erase index, 4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3) := by
  classical
  let center := quadrupoleCenter family.patchMotion time index
  let density := quadrupoleDensity scales family.patchMotion time index
  let selected := quadrupolePatchLabels index
  let velocity := fun position => biotSavart (family.vorticity time) position - biotSavart density position
  let coefficient := Section6.vorticityComplexStrain (externalPatchVorticity scales family.patchMotion time index) center
  let hessian := ∑ source ∈ Finset.univ.erase index, 4 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 3)
  have hessianNonnegative : 0 ≤ hessian := Finset.sum_nonneg fun source member =>
    div_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)
      (mul_nonneg Real.pi_pos.le (pow_nonneg (positive source member).le _))
  have densityIdentity : density = family.subfamilyVorticity selected time := family.quadrupoleDensity_eq_subfamily scales densityEquation time index
  have velocityIdentity (position : ℂ) : velocity position = biotSavart (externalPatchVorticity scales family.patchMotion time index) position := by
    dsimp only [velocity, density]
    rw [← family.patchVorticity_eq scales densityEquation, evolution.patchVorticity_biotSavart_internal_external timeInside index position,
      evolution.quadrupole_biotSavart_eq_sum_patch timeInside index position]
    abel
  have densityContinuousVelocity : Continuous (biotSavart density) := by
    rw [densityIdentity]
    apply continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
      (family.subfamilyVorticity_memLp selected time (ENNReal.ofReal (4 : ℝ))) (by norm_num)
      (show 0 ≤ ∑ label : Fin (count * 4), (‖(family.patch label).center time‖ + 2 * (family.patch label).radius) from
        Finset.sum_nonneg fun label _ => add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (family.patch label).radius_positive.le))
    exact family.subfamilyVorticity_support selected time
  have velocityContinuous : Continuous velocity := (family.biotSavart_continuous time).sub densityContinuousVelocity
  have massIntegrable : Integrable density := evolution.quadrupoleDensity_integrable timeInside index
  have firstIntegrable : Integrable (fun position => density position • (position - center)) := by
    rw [densityIdentity]
    exact family.subfamily_continuous_weight_integrable selected time _ (continuous_id.sub continuous_const)
  have complexMomentIntegrable : Integrable (fun position => density position • (position - center) ^ 2) := by
    rw [densityIdentity]
    exact family.subfamily_continuous_weight_integrable selected time _ ((continuous_id.sub continuous_const).pow 2)
  have secondIntegrable : Integrable (fun position => |density position| * ‖position - center‖ ^ 2) := by
    have integrable := family.subfamily_continuous_weight_integrable selected time
      (fun position : ℂ => ‖position - center‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2)
    rw [← densityIdentity] at integrable
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using integrable.norm
  have supportBound (position : ℂ) (member : position ∈ Function.support density) : ‖position - center‖ ≤ radius := by
    by_contra failure
    have zero (patch : Fin 4) : patchDensity scales family.patchMotion time index patch position = 0 := by
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
      (evolution.quadrupoleDensity_integral_abs_le timeInside amplitudePositive frequencyPositive ratioPositive index)
      (sq_nonneg radius)).trans_eq (by ring))
  have remainder (position : ℂ) (member : position ∈ Function.support density) :
      ‖velocity position - velocity center - coefficient * star (position - center)‖ ≤ (hessian * radius) * ‖position - center‖ := by
    rw [velocityIdentity, velocityIdentity]
    have actualDerivative := evolution.externalPatch_biotSavart_hasFDerivAt_complexStrain timeInside index distance positive separated
    have estimate := evolution.externalPatch_biotSavart_fderiv_taylor_bound timeInside amplitudePositive frequencyPositive ratioPositive
      index distance positive separated (fun source different => (mul_le_mul_of_nonneg_left (supportBound position member) (by norm_num)).trans (near source different))
    rw [actualDerivative.fderiv] at estimate
    change ‖biotSavart (externalPatchVorticity scales family.patchMotion time index) position -
      biotSavart (externalPatchVorticity scales family.patchMotion time index) center - coefficient * star (position - center)‖ ≤
        hessian * ‖position - center‖ ^ 2 at estimate
    apply estimate.trans
    have product := mul_le_mul_of_nonneg_right (supportBound position member) (mul_nonneg hessianNonnegative (norm_nonneg (position - center)))
    nlinarith only [product]
  have fluxBound := integral_weighted_angular_strain_difference_le massIntegrable center
    (deriv (fun current => quadrupoleCenter family.patchMotion current index) time) coefficient firstIntegrable secondIntegrable
    complexMomentIntegrable velocityContinuous (mul_nonneg hessianNonnegative radiusNonnegative) remainder
  rw [evolution.integral_quadrupoleDensity_first_moment timeInside amplitudePositive frequencyPositive ratioPositive index center,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)] at fluxBound
  have derivative := family.quadrupole_angularImpulse_hasDerivAt_external scales densityEquation inside material index
  rw [derivative.deriv]
  have scaled := mul_le_mul_of_nonneg_left (fluxBound.trans (add_le_add_left
    (mul_le_mul_of_nonneg_left secondBound (mul_nonneg hessianNonnegative radiusNonnegative)) _)) (by norm_num : (0 : ℝ) ≤ 2)
  have integralIdentity :
      (∫ position, @inner ℝ ℂ _ (position - center) (density position • (velocity position -
        deriv (fun current => quadrupoleCenter family.patchMotion current index) time))) =
      ∫ position, @inner ℝ ℂ _ (position - center) (density position • (biotSavart (family.vorticity time) position -
        biotSavart density position - deriv (fun current => quadrupoleCenter family.patchMotion current index) time)) := rfl
  rw [integralIdentity] at scaled
  have absoluteScale (first second : ℝ) : |2 * first - 2 * second| = 2 * |first - second| := by
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [absoluteScale]
  dsimp only [center, density, coefficient, hessian] at scaled ⊢
  rw [velocityIdentity center] at scaled
  convert scaled using 1 <;> ring

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
