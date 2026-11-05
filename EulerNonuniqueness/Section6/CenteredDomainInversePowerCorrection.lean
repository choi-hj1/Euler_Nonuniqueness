import EulerNonuniqueness.Section6.InversePowerRemainderTranslation

noncomputable section

open Set MeasureTheory

namespace EulerNonuniqueness.Section6

set_option maxHeartbeats 1000000

def centeredDomainInversePowerCorrection (domain : Set ℂ) (center receiver : ℂ) (power : ℕ) : ℂ :=
  (∫ source in domain, (star (receiver - source))⁻¹ ^ (power + 1)) -
    volume.real domain • (star (receiver - center))⁻¹ ^ (power + 1)

theorem integrableOn_conjugate_inverse_power_of_separation {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (receiver : ℂ) (power : ℕ) {distance : ℝ} (positive : 0 < distance)
    (separated : ∀ source ∈ domain, distance ≤ ‖receiver - source‖) :
    IntegrableOn (fun source => (star (receiver - source))⁻¹ ^ (power + 1)) domain := by
  have majorant : IntegrableOn (fun _ : ℂ => distance⁻¹ ^ (power + 1)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have measurableKernel : Measurable (fun source : ℂ => (star (receiver - source))⁻¹ ^ (power + 1)) := by
    fun_prop
  apply majorant.mono' measurableKernel.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurable] with source member
  rw [norm_pow, norm_inv, norm_star]
  exact pow_le_pow_left₀ (by positivity) (inv_anti₀ positive (separated source member)) (power + 1)

theorem integrableOn_centered_identity_of_bound {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (center : ℂ) {radius : ℝ} (bounded : ∀ source ∈ domain, ‖source - center‖ ≤ radius) :
    IntegrableOn (fun source => source - center) domain := by
  have majorant : IntegrableOn (fun _ : ℂ => radius) domain := integrableOn_const.mpr (Or.inr finite)
  have measurableFunction : Measurable (fun source : ℂ => source - center) := by fun_prop
  apply majorant.mono' measurableFunction.aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurable] with source member
  exact bounded source member

theorem integrableOn_conjugate_inverse_power_taylor_remainder {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (center receiver : ℂ) (power : ℕ) {radius distance : ℝ} (positive : 0 < distance)
    (bounded : ∀ source ∈ domain, ‖source - center‖ ≤ radius)
    (separated : radius + distance ≤ ‖receiver - center‖) :
    IntegrableOn (fun source => conjugateInversePowerTaylorRemainder (receiver - center) power (source - center)) domain := by
  have sourceGap (source : ℂ) (member : source ∈ domain) : distance ≤ ‖receiver - source‖ := by
    have triangle := norm_add_le (receiver - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith [bounded source member]
  have kernel := integrableOn_conjugate_inverse_power_of_separation measurable finite receiver power positive sourceGap
  have base : IntegrableOn (fun _ : ℂ => (star (receiver - center))⁻¹ ^ (power + 1)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have centered := integrableOn_centered_identity_of_bound measurable finite center bounded
  have conjugated : IntegrableOn (fun source : ℂ => star (source - center)) domain := by
    simpa only [Complex.conjCLE_apply, starRingEnd_apply] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp centered
  have linear := conjugated.const_mul ((power + 1 : ℂ) * (star (receiver - center))⁻¹ ^ (power + 2))
  have identity : (fun source : ℂ => conjugateInversePowerTaylorRemainder (receiver - center) power (source - center)) =
      fun source => (star (receiver - source))⁻¹ ^ (power + 1) - (star (receiver - center))⁻¹ ^ (power + 1) -
        ((power + 1 : ℂ) * (star (receiver - center))⁻¹ ^ (power + 2)) * star (source - center) := by
    funext source
    simp only [conjugateInversePowerTaylorRemainder]
    rw [show (receiver - center) - (source - center) = receiver - source by abel]
  rw [identity]
  exact (kernel.sub base).sub linear

theorem centeredDomainInversePowerCorrection_eq_integral_remainder {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (center receiver : ℂ) (power : ℕ) {radius distance : ℝ} (positive : 0 < distance)
    (bounded : ∀ source ∈ domain, ‖source - center‖ ≤ radius)
    (separated : radius + distance ≤ ‖receiver - center‖)
    (centered : (∫ source in domain, source - center) = 0) :
    centeredDomainInversePowerCorrection domain center receiver power =
      ∫ source in domain, conjugateInversePowerTaylorRemainder (receiver - center) power (source - center) := by
  have sourceGap (source : ℂ) (member : source ∈ domain) : distance ≤ ‖receiver - source‖ := by
    have triangle := norm_add_le (receiver - source) (source - center)
    rw [sub_add_sub_cancel] at triangle
    linarith [bounded source member]
  have kernel := integrableOn_conjugate_inverse_power_of_separation measurable finite receiver power positive sourceGap
  have base : IntegrableOn (fun _ : ℂ => (star (receiver - center))⁻¹ ^ (power + 1)) domain :=
    integrableOn_const.mpr (Or.inr finite)
  have firstMoment := integrableOn_centered_identity_of_bound measurable finite center bounded
  have conjugated : IntegrableOn (fun source : ℂ => star (source - center)) domain := by
    simpa only [Complex.conjCLE_apply, starRingEnd_apply] using
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).integrable_comp firstMoment
  have linear := conjugated.const_mul ((power + 1 : ℂ) * (star (receiver - center))⁻¹ ^ (power + 2))
  have identity (source : ℂ) :
      conjugateInversePowerTaylorRemainder (receiver - center) power (source - center) =
        (star (receiver - source))⁻¹ ^ (power + 1) - (star (receiver - center))⁻¹ ^ (power + 1) -
          ((power + 1 : ℂ) * (star (receiver - center))⁻¹ ^ (power + 2)) * star (source - center) := by
    unfold conjugateInversePowerTaylorRemainder
    rw [show (receiver - center) - (source - center) = receiver - source by abel]
  simp_rw [identity]
  have split := integral_sub (kernel.sub base) linear
  simp only [Pi.sub_apply] at split
  rw [split, integral_sub kernel base, integral_const, integral_const_mul]
  have conjugateZero : (∫ source in domain, star (source - center)) = 0 := by
    simpa only [Complex.star_def, integral_conj, centered, map_zero]
  rw [conjugateZero, mul_zero, sub_zero]
  simp only [centeredDomainInversePowerCorrection, Measure.real, Measure.restrict_apply_univ]

theorem centeredDomainInversePowerCorrection_receiver_difference_norm_le {domain : Set ℂ}
    (measurable : MeasurableSet domain) (finite : volume domain < ⊤)
    (center anchor first second : ℂ) (power : ℕ) {radius travel distance : ℝ}
    (radiusNonnegative : 0 ≤ radius) (travelNonnegative : 0 ≤ travel) (positive : 0 < distance)
    (bounded : ∀ source ∈ domain, ‖source - center‖ ≤ radius)
    (separated : radius + travel + distance ≤ ‖anchor - center‖)
    (firstBound : ‖first - anchor‖ ≤ travel) (secondBound : ‖second - anchor‖ ≤ travel)
    (centered : (∫ source in domain, source - center) = 0) :
    ‖centeredDomainInversePowerCorrection domain center first power -
      centeredDomainInversePowerCorrection domain center second power‖ ≤
      volume.real domain *
        ((power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius ^ 2) *
          ‖first - second‖ := by
  have receiverSeparated (receiver : ℂ) (near : ‖receiver - anchor‖ ≤ travel) :
      radius + distance ≤ ‖receiver - center‖ := by
    have triangle := norm_add_le (anchor - receiver) (receiver - center)
    rw [sub_add_sub_cancel, norm_sub_rev anchor receiver] at triangle
    linarith
  rw [centeredDomainInversePowerCorrection_eq_integral_remainder measurable finite center first power positive bounded
      (receiverSeparated first firstBound) centered,
    centeredDomainInversePowerCorrection_eq_integral_remainder measurable finite center second power positive bounded
      (receiverSeparated second secondBound) centered,
    ← integral_sub
      (integrableOn_conjugate_inverse_power_taylor_remainder measurable finite center first power positive bounded
        (receiverSeparated first firstBound))
      (integrableOn_conjugate_inverse_power_taylor_remainder measurable finite center second power positive bounded
        (receiverSeparated second secondBound))]
  have estimate := norm_integral_le_of_norm_le (μ := volume.restrict domain)
    (show Integrable (fun _ : ℂ =>
      ((power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) * distance⁻¹ ^ (power + 4) * radius ^ 2) *
        ‖first - second‖) (volume.restrict domain) from integrableOn_const.mpr (Or.inr finite)) (by
      filter_upwards [ae_restrict_mem measurable] with source member
      have actual := conjugateInversePowerTaylorRemainder_receiver_difference_bound
        (anchor - center) (first - center) (second - center) (source - center) power
        radiusNonnegative travelNonnegative positive separated (bounded source member)
        (by simpa only [sub_sub_sub_cancel_right] using firstBound)
        (by simpa only [sub_sub_sub_cancel_right] using secondBound)
      simp only [sub_sub_sub_cancel_right] at actual
      apply actual.trans
      have scalar := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (bounded source member)
          (show 0 ≤ (power + 1 : ℝ) * (power + 2 : ℝ) * (power + 3 : ℝ) *
            distance⁻¹ ^ (power + 4) * radius by positivity)) (norm_nonneg (first - second))
      convert scalar using 1 <;> ring)
  simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_assoc] using estimate

end EulerNonuniqueness.Section6
