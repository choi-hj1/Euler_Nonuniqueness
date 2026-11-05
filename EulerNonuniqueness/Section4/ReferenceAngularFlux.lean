import EulerNonuniqueness.Section6.MovingQuadrupoleAngularMoment
import EulerNonuniqueness.Section6.PaperQuadrupoleStaticMoments
import EulerNonuniqueness.General.WeightedAngularFluxBound

noncomputable section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace EulerNonuniqueness.Paper.FiniteMovingPatchFamily

set_option maxHeartbeats 1000000

theorem quadrupole_angularImpulse_deriv_bound {count : ℕ}
    (family : FiniteMovingPatchFamily (count * 4)) (scales : Scales)
    (densityEquation : ∀ (index : Fin count) (patch : Fin 4),
      family.density (finProdFinEquiv (index, patch)) =
        patchSign patch * scales.amplitude * scales.omega (index.val + 1) ^ 4)
    {horizon time radius : ℝ} {strain : ℝ≥0}
    (evolution : FinitePatchEvolution scales family.patchMotion horizon) (timeInside : time ∈ Icc 0 horizon)
    (amplitudePositive : 0 < scales.amplitude) (frequencyPositive : 0 < scales.frequency)
    (ratioPositive : 0 < scales.ratio)
    (inside : ∀ index, time ∈ Ioo (family.patch index).initialTime (family.patch index).finalTime)
    (material : ∀ index label, (family.patch index).boundaryVelocity time label =
      biotSavart (family.vorticity time) ((family.patch index).boundary time label))
    (index : Fin count) (radiusNonnegative : 0 ≤ radius)
    (sourceBounded : ∀ patch, family.patchMotion.domain time index patch ⊆
      Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius)
    (distance : Fin count → ℝ)
    (positive : ∀ source ∈ Finset.univ.erase index, 0 < distance source)
    (separated : ∀ position ∈ Metric.closedBall (quadrupoleCenter family.patchMotion time index) radius,
      ∀ source ∈ Finset.univ.erase index, ∀ patch,
      ∀ location ∈ family.patchMotion.domain time source patch, distance source ≤ ‖position - location‖)
    (strainBound : (∑ source ∈ Finset.univ.erase index,
      2 * scales.circulation (source.val + 1) / (Real.pi * distance source ^ 2)) ≤ (strain : ℝ)) :
    |deriv (fun current => angularImpulse scales family.patchMotion current index) time| ≤
      8 * scales.circulation (index.val + 1) *
        ‖centroidAsymmetry family.patchMotion time index‖ *
          ‖biotSavart (externalPatchVorticity scales family.patchMotion time index)
              (quadrupoleCenter family.patchMotion time index) -
            deriv (fun current => quadrupoleCenter family.patchMotion current index) time‖ +
        8 * scales.circulation (index.val + 1) * (strain : ℝ) * radius ^ 2 := by
  classical
  let center := quadrupoleCenter family.patchMotion time index
  let density := quadrupoleDensity scales family.patchMotion time index
  let selected := quadrupolePatchLabels index
  let velocity := fun position => biotSavart (family.vorticity time) position - biotSavart density position
  have densityIdentity : density = family.subfamilyVorticity selected time :=
    family.quadrupoleDensity_eq_subfamily scales densityEquation time index
  have velocityIdentity (position : ℂ) : velocity position =
      biotSavart (externalPatchVorticity scales family.patchMotion time index) position := by
    dsimp only [velocity, density]
    rw [← family.patchVorticity_eq scales densityEquation,
      evolution.patchVorticity_biotSavart_internal_external timeInside index position,
      evolution.quadrupole_biotSavart_eq_sum_patch timeInside index position]
    abel
  have densityContinuousVelocity : Continuous (biotSavart density) := by
    rw [densityIdentity]
    apply continuous_biotSavart_of_memLp_support holderConjugate_four_fourThirds
      (family.subfamilyVorticity_memLp selected time (ENNReal.ofReal (4 : ℝ))) (by norm_num)
      (show 0 ≤ ∑ label : Fin (count * 4), (‖(family.patch label).center time‖ +
        2 * (family.patch label).radius) from Finset.sum_nonneg fun label _ =>
          add_nonneg (norm_nonneg _) (mul_nonneg (by norm_num) (family.patch label).radius_positive.le))
    exact family.subfamilyVorticity_support selected time
  have velocityContinuous : Continuous velocity := (family.biotSavart_continuous time).sub densityContinuousVelocity
  have massIntegrable : Integrable density := evolution.quadrupoleDensity_integrable timeInside index
  have firstIntegrable : Integrable (fun position => density position • (position - center)) := by
    rw [densityIdentity]
    exact family.subfamily_continuous_weight_integrable selected time _ (continuous_id.sub continuous_const)
  have secondIntegrable : Integrable (fun position => |density position| * ‖position - center‖ ^ 2) := by
    have integrable := family.subfamily_continuous_weight_integrable selected time
      (fun position : ℂ => ‖position - center‖ ^ 2) ((continuous_id.sub continuous_const).norm.pow 2)
    rw [← densityIdentity] at integrable
    simpa only [smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using integrable.norm
  have supportBound (position : ℂ) (member : position ∈ Function.support density) : ‖position - center‖ ≤ radius := by
    by_contra notBounded
    have zero (patch : Fin 4) : patchDensity scales family.patchMotion time index patch position = 0 := by
      apply indicator_of_not_mem
      intro patchMember
      exact notBounded (by simpa only [Metric.mem_closedBall, dist_eq_norm] using sourceBounded patch patchMember)
    exact member (by simp only [density, quadrupoleDensity, zero, Finset.sum_const_zero])
  have secondBound : (∫ position, |density position| * ‖position - center‖ ^ 2) ≤
      4 * scales.circulation (index.val + 1) * radius ^ 2 := by
    have estimate := integral_mono_ae secondIntegrable (massIntegrable.norm.const_mul (radius ^ 2))
      (Filter.Eventually.of_forall fun position => by
        by_cases zero : density position = 0
        · simp [zero]
        · exact (mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (supportBound position zero) 2) (abs_nonneg _)).trans_eq (mul_comm _ _))
    rw [integral_const_mul] at estimate
    exact estimate.trans ((mul_le_mul_of_nonneg_left
      (evolution.quadrupoleDensity_integral_abs_le timeInside amplitudePositive frequencyPositive ratioPositive index)
      (sq_nonneg radius)).trans_eq (by ring))
  have lipschitz := evolution.externalPatch_biotSavart_lipschitzOn timeInside amplitudePositive frequencyPositive
    ratioPositive index distance (Metric.closedBall center radius) positive separated strainBound
  have fluxBound := abs_integral_weighted_angular_flux_le massIntegrable center
    (deriv (fun current => quadrupoleCenter family.patchMotion current index) time)
    firstIntegrable secondIntegrable velocityContinuous strain.property (by
      intro position member
      rw [velocityIdentity, velocityIdentity]
      exact lipschitz.norm_sub_le
        (by simpa only [Metric.mem_closedBall, dist_eq_norm] using supportBound position member)
        (Metric.mem_closedBall_self radiusNonnegative))
  rw [evolution.integral_quadrupoleDensity_first_moment timeInside amplitudePositive frequencyPositive
    ratioPositive index center, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by norm_num) (scales.circulation_pos frequencyPositive ratioPositive _).le)] at fluxBound
  have derivative := family.quadrupole_angularImpulse_hasDerivAt_external scales densityEquation inside material index
  rw [derivative.deriv, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have estimate := mul_le_mul_of_nonneg_left
    (fluxBound.trans (add_le_add_left (mul_le_mul_of_nonneg_left secondBound strain.property) _)) (by norm_num : (0 : ℝ) ≤ 2)
  rw [← velocityIdentity center]
  dsimp only [velocity, center, density] at estimate ⊢
  have arithmetic (mass asymmetry speed rate size : ℝ) :
      2 * (4 * mass * asymmetry * speed + rate * (4 * mass * size ^ 2)) =
        8 * mass * asymmetry * speed + 8 * mass * rate * size ^ 2 := by ring
  rw [arithmetic] at estimate
  exact estimate

end EulerNonuniqueness.Paper.FiniteMovingPatchFamily
