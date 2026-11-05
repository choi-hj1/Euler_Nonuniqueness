import EulerNonuniqueness.Section3.ExteriorCentroidResponse
import EulerNonuniqueness.Section3.ContourPolynomialDomainMoment
import EulerNonuniqueness.Section3.SimilarityPatchDomain
import EulerNonuniqueness.Section6.ExteriorBiotSavartSeries

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000

attribute [local instance] c1InverseAnalyticGroup c1InverseAnalyticSpace

theorem exterior_biotSavart_normalized_domain_integral
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (center : ℂ) {radius distance : ℝ} (radiusPositive : 0 < radius)
    (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (smallRadius : 24 * radius / distance < 1) (phase : Circle)
    (data : PeriodicC1HolderHalf) (nearby : ‖data - standardCircleBanach‖ < 1 / 3) :
    (∫ position in nearCircleInterior data nearby,
      (radius : ℂ)⁻¹ *
        (biotSavart vorticity (center + (radius : ℂ) * ((phase : ℂ) * position)) -
          biotSavart vorticity center)) =
      (Real.pi : ℂ) * (phase : ℂ) * contourExteriorCentroidResponse phase
        (fun power => Section6.exteriorVorticityCoefficient vorticity center radius power) data := by
  let domain := nearCircleInterior data nearby
  let coefficient := fun power : ℕ => Section6.exteriorVorticityCoefficient vorticity center radius power
  let terms := fun power : ℕ => fun position : ℂ => coefficient power *
    (star ((phase : ℂ) * position)) ^ (power + 1)
  let bounds := fun power : ℕ => fun _ : ℂ => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖
  have domainMeasurable : MeasurableSet domain := (nearCircleInterior_isOpen data nearby).measurableSet
  have domainFinite : volume domain < ⊤ := (nearCircleInterior_isBounded data nearby).measure_lt_top
  have weighted : Summable (fun power : ℕ => (24 : ℝ) ^ (power + 1) * ‖coefficient power‖) :=
    Section6.summable_exteriorVorticityCoefficient_weight integrable center radiusPositive.le
      distancePositive (by norm_num) separated smallRadius
  have positionBound (position : ℂ) (member : position ∈ domain) : ‖position‖ ≤ 24 := by
    have actual := nearCircleInterior_subset_ball data nearby member
    rw [mem_ball_zero_iff] at actual
    linarith
  have termBound (power : ℕ) : ∀ᵐ position ∂volume.restrict domain,
      ‖terms power position‖ ≤ bounds power position := by
    filter_upwards [ae_restrict_mem domainMeasurable] with position member
    dsimp only [terms, bounds]
    rw [norm_mul, norm_pow, norm_star, norm_mul, Circle.norm_coe, one_mul]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (positionBound position member) _)
      (norm_nonneg _)).trans_eq (mul_comm _ _)
  have pointwise : ∀ᵐ position ∂volume.restrict domain,
      HasSum (fun power => terms power position)
        ((radius : ℂ)⁻¹ *
          (biotSavart vorticity (center + (radius : ℂ) * ((phase : ℂ) * position)) -
            biotSavart vorticity center)) := by
    filter_upwards [ae_restrict_mem domainMeasurable] with position member
    apply Section6.exterior_biotSavart_series_hasSum integrable membership center
      ((phase : ℂ) * position) radiusPositive distancePositive separated
    rw [norm_mul, Circle.norm_coe, one_mul]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (positionBound position member) radiusPositive.le)
      distancePositive.le).trans_lt (by simpa only [mul_comm radius 24] using smallRadius)
  have summed := hasSum_integral_of_dominated_convergence (μ := volume.restrict domain) bounds
    (fun power => by dsimp only [terms]; exact (by fun_prop : Continuous _).aestronglyMeasurable)
    termBound (Filter.Eventually.of_forall fun _ => weighted)
    (show Integrable (fun position => ∑' power, bounds power position) (volume.restrict domain) from
      by dsimp only [bounds]; exact integrableOn_const.mpr (Or.inr domainFinite)) pointwise
  have termIntegral (power : ℕ) : (∫ position in domain, terms power position) =
      (Real.pi : ℂ) * (phase : ℂ) *
        (((phase : ℂ)⁻¹ ^ (power + 2) * coefficient power) *
          (star (contourPolynomialMoment (power + 1) data) / (Real.pi : ℂ))) := by
    have identity : terms power = fun position : ℂ =>
        (coefficient power * (star (phase : ℂ)) ^ (power + 1)) * star (position ^ (power + 1)) := by
      funext position
      simp only [terms, star_mul, star_pow, mul_pow]
      ring
    have conjugateIntegral : (∫ position in domain, star (position ^ (power + 1))) =
        star (∫ position in domain, position ^ (power + 1)) := by
      simpa only using (integral_conj (f := fun position : ℂ => position ^ (power + 1))
        (μ := volume.restrict domain))
    rw [identity, integral_const_mul, conjugateIntegral,
      ← contourPolynomialMoment_eq_domain_integral (power + 1) data nearby]
    rw [show star (phase : ℂ) = (phase : ℂ)⁻¹ from (Circle.coe_inv_eq_conj phase).symm]
    have phaseNonzero : (phase : ℂ) ≠ 0 := Circle.coe_ne_zero phase
    have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp only [show power + 2 = (power + 1) + 1 by omega, pow_succ]
    field_simp
    <;> ring
  simp_rw [termIntegral] at summed
  have actual := summed.tsum_eq
  rw [tsum_mul_left] at actual
  exact actual.symm

theorem exterior_biotSavart_domain_average_eq_response
    {vorticity : Vorticity} (integrable : Integrable vorticity)
    (membership : MemLp vorticity (ENNReal.ofReal (4 : ℝ)) volume)
    (fieldContinuous : Continuous (biotSavart vorticity))
    (center : ℂ) {radius distance : ℝ} (radiusPositive : 0 < radius)
    (distancePositive : 0 < distance)
    (separated : ∀ source ∈ Function.support vorticity, distance ≤ ‖center - source‖)
    (smallRadius : 24 * radius / distance < 1) (phase : Circle)
    (data : PeriodicC1HolderHalf) (nearby : ‖data - standardCircleBanach‖ < 1 / 3)
    (area : contourAreaFunctional data = Real.pi) :
    (Real.pi * radius ^ 2)⁻¹ •
        (∫ position in similarityPatchDomain center radius phase data nearby,
          biotSavart vorticity position) - biotSavart vorticity center =
      radius • ((phase : ℂ) * contourExteriorCentroidResponse phase
        (fun power => Section6.exteriorVorticityCoefficient vorticity center radius power) data) := by
  let domain := nearCircleInterior data nearby
  have domainFinite : volume domain < ⊤ := (nearCircleInterior_isBounded data nearby).measure_lt_top
  have domainVolume : volume.real domain = Real.pi := by
    change (volume (nearCircleInterior data nearby)).toReal = Real.pi
    rw [← contourAreaFunctional_eq_domain_area data nearby, area]
  have pulledIntegrable : IntegrableOn (fun position : ℂ =>
      biotSavart vorticity (center + (radius : ℂ) * ((phase : ℂ) * position))) domain :=
    ((fieldContinuous.comp (by fun_prop)).continuousOn.integrableOn_compact
      (nearCircleInterior_isBounded data nearby).isCompact_closure).mono_set subset_closure
  have constantIntegrable : IntegrableOn (fun _ : ℂ => biotSavart vorticity center) domain :=
    integrableOn_const.mpr (Or.inr domainFinite)
  have actual := exterior_biotSavart_normalized_domain_integral integrable membership center
    radiusPositive distancePositive separated smallRadius phase data nearby
  rw [integral_const_mul, integral_sub pulledIntegrable constantIntegrable,
    setIntegral_const, domainVolume] at actual
  rw [integral_similarityPatchDomain center radiusPositive phase data nearby]
  simp only [Complex.real_smul, map_inv₀, map_mul, map_pow] at actual ⊢
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr radiusPositive.ne'
  have piNonzero : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have multiplied := congrArg (fun value : ℂ => (radius : ℂ) * value / (Real.pi : ℂ)) actual
  dsimp only [domain] at multiplied
  simp only [mul_assoc] at multiplied ⊢
  field_simp at multiplied ⊢
  linear_combination (radius : ℂ) ^ 2 * multiplied

end EulerNonuniqueness.Paper
