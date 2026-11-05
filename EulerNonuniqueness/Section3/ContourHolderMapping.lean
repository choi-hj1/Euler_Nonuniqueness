import EulerNonuniqueness.Section3.ContourCauchyPeriodic

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem standardCircle_chord_bound_centered {target source : ℝ}
    (nearby : |source - target| ≤ Real.pi) :
    (2 / Real.pi) * |source - target| ≤ ‖standardCircle source - standardCircle target‖ := by
  have identity : standardCircle source - standardCircle target =
      (standardCircle (source - target) - standardCircle 0) * standardCircle target := by
    rw [sub_mul, ← standardCircle_add, sub_add_cancel]
    simp [standardCircle]
  rw [identity, norm_mul, standardCircle_norm, mul_one]
  exact standardCircle_chord_bound _ ⟨(abs_le.mp nearby).1, (abs_le.mp nearby).2⟩

theorem contour_near_circle_chord_bound {curve tangent : ℝ → ℂ} {difference target source : ℝ}
    (derivative : ∀ current : ℝ, HasDerivAt curve (tangent current) current)
    (derivative_difference : ∀ current : ℝ,
      ‖tangent current - standardCircleTangent current‖ ≤ difference)
    (nearby : |source - target| ≤ Real.pi) :
    (2 / Real.pi - difference) * |source - target| ≤ ‖curve target - curve source‖ := by
  have actual := contour_chord_lower_of_derivative_close
    (show target ∈ Icc (min target source) (max target source) from ⟨min_le_left _ _, le_max_left _ _⟩)
    (show source ∈ Icc (min target source) (max target source) from ⟨min_le_right _ _, le_max_right _ _⟩)
    (fun current _ => derivative current) (fun current _ => standardCircle_derivative current)
    (fun current _ => derivative_difference current) (standardCircle_chord_bound_centered nearby)
  rwa [norm_sub_rev] at actual

theorem contourCauchyDensityRemainder_bound_unordered {curve tangent density : ℝ → ℂ}
    {target source holder speed chord : ℝ} (holder_nonneg : 0 ≤ holder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (density_bound : ‖density source - density target‖ ≤ holder * Real.sqrt |source - target|)
    (tangent_bound : ‖tangent source‖ ≤ speed)
    (chord_bound : chord * |source - target| ≤ ‖curve target - curve source‖) :
    ‖contourCauchyDensityRemainder curve tangent density target source‖ ≤
      (holder * speed / chord) * inverseSqrtDistance target source := by
  by_cases equal : source = target
  · subst source
    simp [contourCauchyDensityRemainder, inverseSqrtDistance]
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr equal)
  have root_pos := Real.sqrt_pos.mpr distance_pos
  simp only [contourCauchyDensityRemainder, norm_div, norm_mul, inverseSqrtDistance]
  calc
    _ ≤ (holder * Real.sqrt |source - target| * speed) / ‖curve target - curve source‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul density_bound tangent_bound (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ ≤ (holder * Real.sqrt |source - target| * speed) / (chord * |source - target|) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos chord_pos distance_pos) chord_bound
    _ = _ := by
      field_simp
      calc
        _ = holder * speed * chord * (Real.sqrt |source - target| ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt distance_pos.le]; ring

theorem contourCauchyDensityRemainder_integrable_interval {curve tangent density : ℝ → ℂ}
    {target lower upper holder speed chord : ℝ} (holder_nonneg : 0 ≤ holder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (density_continuous : Continuous density)
    (density_bound : ∀ source ∈ Icc lower upper,
      ‖density source - density target‖ ≤ holder * Real.sqrt |source - target|)
    (tangent_bound : ∀ source ∈ Icc lower upper, ‖tangent source‖ ≤ speed)
    (chord_bound : ∀ source ∈ Icc lower upper,
      chord * |source - target| ≤ ‖curve target - curve source‖) :
    IntegrableOn (contourCauchyDensityRemainder curve tangent density target) (Icc lower upper) volume := by
  apply weakSingular_integrable
    ((((density_continuous.measurable.sub measurable_const).mul tangent_continuous.measurable).div
      (measurable_const.sub curve_continuous.measurable)).aestronglyMeasurable)
  intro source membership
  exact contourCauchyDensityRemainder_bound_unordered holder_nonneg speed_nonneg chord_pos
    (density_bound source membership) (tangent_bound source membership) (chord_bound source membership)

theorem contourCauchyDensityRemainder_near_bound {curve tangent density : ℝ → ℂ}
    {target radius holder speed chord : ℝ} {domain : Set ℝ}
    (radius_pos : 0 < radius) (holder_nonneg : 0 ≤ holder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (domain_measurable : MeasurableSet domain)
    (domain_near : domain ⊆ Ioo (target - radius) (target + radius))
    (density_bound : ∀ source ∈ domain,
      ‖density source - density target‖ ≤ holder * Real.sqrt |source - target|)
    (tangent_bound : ∀ source ∈ domain, ‖tangent source‖ ≤ speed)
    (chord_bound : ∀ source ∈ domain,
      chord * |source - target| ≤ ‖curve target - curve source‖) :
    ‖∫ source in domain, contourCauchyDensityRemainder curve tangent density target source‖ ≤
      4 * (holder * speed / chord) * Real.sqrt radius := by
  apply norm_setIntegral_weakSingular_near radius_pos (by positivity) domain_measurable domain_near
  intro source membership
  exact contourCauchyDensityRemainder_bound_unordered holder_nonneg speed_nonneg chord_pos
    (density_bound source membership) (tangent_bound source membership) (chord_bound source membership)

theorem contourCauchy_density_far_difference_bound {curve tangent density : ℝ → ℂ}
    {first second source speed chord holder : ℝ}
    (distinct : first ≠ source) (speed_nonneg : 0 ≤ speed)
    (chord_pos : 0 < chord) (holder_nonneg : 0 ≤ holder)
    (nearby : |first - second| ≤ |first - source| / 2)
    (tangent_bound : ‖tangent source‖ ≤ speed)
    (target_lipschitz : ‖curve first - curve second‖ ≤ speed * |first - second|)
    (first_chord : chord * |first - source| ≤ ‖curve first - curve source‖)
    (second_chord : chord * |second - source| ≤ ‖curve second - curve source‖)
    (density_bound : ‖density source - density first‖ ≤ holder * Real.sqrt |first - source|) :
    ‖(contourCauchyKernel curve tangent first source - contourCauchyKernel curve tangent second source) *
        (density source - density first)‖ ≤
      (2 * speed ^ 2 * holder / chord ^ 2) * |first - second| * |first - source| ^ (-(3 / 2 : ℝ)) := by
  have distance_pos : 0 < |first - source| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  rw [norm_mul]
  calc
    _ ≤ ((2 * speed ^ 2 / chord ^ 2) * |first - second| / |first - source| ^ 2) *
        (holder * Real.sqrt |first - source|) :=
      mul_le_mul (contourCauchyKernel_far_difference distinct speed_nonneg chord_pos nearby
        tangent_bound target_lipschitz first_chord second_chord) density_bound (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow]
      have power : |first - source| ^ (1 / 2 : ℝ) / |first - source| ^ 2 =
          |first - source| ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_sub distance_pos]
        norm_num
      calc
        _ = (2 * speed ^ 2 * holder / chord ^ 2) * |first - second| *
            (|first - source| ^ (1 / 2 : ℝ) / |first - source| ^ 2) := by ring
        _ = _ := by rw [power]

theorem norm_integral_far_half_bound {integrand : ℝ → ℂ} {cutoff radius bound : ℝ}
    (cutoff_pos : 0 < cutoff) (ordered : cutoff ≤ radius) (bound_nonneg : 0 ≤ bound)
    (majorized : ∀ source ∈ Ioc cutoff radius,
      ‖integrand source‖ ≤ bound * cutoff * source ^ (-(3 / 2 : ℝ))) :
    ‖∫ source in cutoff..radius, integrand source‖ ≤ 2 * bound * Real.sqrt cutoff := by
  have zero_not_mem : (0 : ℝ) ∉ uIcc cutoff radius := by
    rw [uIcc_of_le ordered]
    intro membership
    linarith [membership.1]
  have majorant_integrable : IntervalIntegrable
      (fun source : ℝ => bound * cutoff * source ^ (-(3 / 2 : ℝ))) volume cutoff radius :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr zero_not_mem)).const_mul _
  have estimate := intervalIntegral.norm_integral_le_of_norm_le
    (show ∀ᵐ source ∂volume.restrict (uIoc cutoff radius),
      ‖integrand source‖ ≤ bound * cutoff * source ^ (-(3 / 2 : ℝ)) from by
      rw [uIoc_of_le ordered]
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with source membership
      exact majorized source membership) majorant_integrable
  have nonnegative : 0 ≤ ∫ source in cutoff..radius,
      bound * cutoff * source ^ (-(3 / 2 : ℝ)) := by
    apply intervalIntegral.integral_nonneg ordered
    intro source membership
    exact mul_nonneg (mul_nonneg bound_nonneg cutoff_pos.le)
      (Real.rpow_nonneg (cutoff_pos.le.trans membership.1) _)
  rw [abs_of_nonneg nonnegative] at estimate
  calc
    _ ≤ ∫ source in cutoff..radius, bound * cutoff * source ^ (-(3 / 2 : ℝ)) := estimate
    _ = bound * ∫ source in cutoff..radius, cutoff * source ^ (-(3 / 2 : ℝ)) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext source
      ring
    _ ≤ bound * (2 * Real.sqrt cutoff) :=
      mul_le_mul_of_nonneg_left (contourCauchy_far_majorant_integral cutoff_pos ordered) bound_nonneg
    _ = _ := by ring

theorem contourCauchy_density_far_integral_bound {curve tangent density : ℝ → ℂ}
    {second radius speed chord holder : ℝ} (second_ne : second ≠ 0)
    (ordered : 2 * |second| ≤ radius) (speed_nonneg : 0 ≤ speed)
    (chord_pos : 0 < chord) (holder_nonneg : 0 ≤ holder)
    (tangent_bound : ∀ source ∈ Ioc (2 * |second|) radius, ‖tangent source‖ ≤ speed)
    (target_lipschitz : ‖curve 0 - curve second‖ ≤ speed * |second|)
    (first_chord : ∀ source ∈ Ioc (2 * |second|) radius,
      chord * source ≤ ‖curve 0 - curve source‖)
    (second_chord : ∀ source ∈ Ioc (2 * |second|) radius,
      chord * |second - source| ≤ ‖curve second - curve source‖)
    (density_bound : ∀ source ∈ Ioc (2 * |second|) radius,
      ‖density source - density 0‖ ≤ holder * Real.sqrt source) :
    ‖∫ source in (2 * |second|)..radius,
      (contourCauchyKernel curve tangent 0 source - contourCauchyKernel curve tangent second source) *
        (density source - density 0)‖ ≤
      (2 * speed ^ 2 * holder / chord ^ 2) * Real.sqrt (2 * |second|) := by
  have cutoff_pos : 0 < 2 * |second| := mul_pos (by norm_num) (abs_pos.mpr second_ne)
  have estimate := norm_integral_far_half_bound cutoff_pos ordered
    (show 0 ≤ speed ^ 2 * holder / chord ^ 2 by positivity)
    (integrand := fun source =>
      (contourCauchyKernel curve tangent 0 source - contourCauchyKernel curve tangent second source) *
        (density source - density 0)) ?_
  · convert estimate using 1 <;> ring
  intro source membership
  have source_pos : 0 < source := cutoff_pos.trans membership.1
  have distance : |(0 : ℝ) - source| = source := by rw [zero_sub, abs_neg, abs_of_pos source_pos]
  have actual := contourCauchy_density_far_difference_bound
    (show (0 : ℝ) ≠ source by linarith) speed_nonneg chord_pos holder_nonneg
    (show |(0 : ℝ) - second| ≤ |(0 : ℝ) - source| / 2 by
      rw [zero_sub, abs_neg, distance]
      linarith [membership.1])
    (tangent_bound source membership)
    (by simpa only [zero_sub, abs_neg] using target_lipschitz)
    (by simpa only [distance] using first_chord source membership) (second_chord source membership)
    (by simpa only [distance] using density_bound source membership)
  rw [distance, zero_sub, abs_neg] at actual
  convert actual using 1 <;> ring

noncomputable def contourCauchyTransform (curve tangent density : ℝ → ℂ) (target : ℝ) : ℂ :=
  (∫ source in (target - Real.pi)..(target + Real.pi),
    contourCauchyDensityRemainder curve tangent density target source) -
      (Real.pi : ℂ) * Complex.I * density target

theorem truncatedIntegral_tendsto_integral_centered {kernel : ℝ → ℂ} {center radius : ℝ}
    (radius_pos : 0 < radius)
    (integrable : IntervalIntegrable kernel volume (center - radius) (center + radius)) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (center - radius)..(center - cutoff), kernel source) +
        ∫ source in (center + cutoff)..(center + radius), kernel source)
      (𝓝[>] 0) (𝓝 (∫ source in (center - radius)..(center + radius), kernel source)) := by
  have shifted : IntervalIntegrable (fun source => kernel (source + center)) volume (-radius) radius := by
    convert integrable.comp_add_right center using 1 <;> congr 1 <;> ring
  have limit := truncatedIntegral_tendsto_integral radius_pos shifted
  simp_rw [intervalIntegral.integral_comp_add_right] at limit
  simpa only [sub_eq_add_neg, add_comm] using limit

theorem principal_value_density_subtraction {kernel density : ℝ → ℂ}
    {center radius : ℝ} {constant : ℂ} (radius_pos : 0 < radius)
    (kernel_continuous : ContinuousOn kernel (Icc (center - radius) (center + radius) \ {center}))
    (remainder_integrable : IntervalIntegrable
      (fun source => (density source - density center) * kernel source)
      volume (center - radius) (center + radius))
    (kernel_limit : Tendsto (fun cutoff : ℝ =>
      (∫ source in (center - radius)..(center - cutoff), kernel source) +
        ∫ source in (center + cutoff)..(center + radius), kernel source)
      (𝓝[>] 0) (𝓝 constant)) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (center - radius)..(center - cutoff), density source * kernel source) +
        ∫ source in (center + cutoff)..(center + radius), density source * kernel source)
      (𝓝[>] 0) (𝓝 ((∫ source in (center - radius)..(center + radius),
        (density source - density center) * kernel source) + density center * constant)) := by
  have remainder_limit := truncatedIntegral_tendsto_integral_centered radius_pos remainder_integrable
  apply (remainder_limit.add (kernel_limit.const_mul (density center))).congr'
  filter_upwards [Ioo_mem_nhdsGT radius_pos] with cutoff cutoff_mem
  have left_subset : Icc (center - radius) (center - cutoff) ⊆
      Icc (center - radius) (center + radius) \ {center} := by
    intro source membership
    refine ⟨⟨membership.1, by linarith [membership.2, cutoff_mem.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.2, cutoff_mem.1]
  have right_subset : Icc (center + cutoff) (center + radius) ⊆
      Icc (center - radius) (center + radius) \ {center} := by
    intro source membership
    refine ⟨⟨by linarith [membership.1, cutoff_mem.1], membership.2⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [membership.1, cutoff_mem.1]
  have left_integrable : IntervalIntegrable kernel volume (center - radius) (center - cutoff) :=
    (kernel_continuous.mono left_subset).intervalIntegrable_of_Icc
    (by linarith [cutoff_mem.2] : center - radius ≤ center - cutoff)
  have right_integrable : IntervalIntegrable kernel volume (center + cutoff) (center + radius) :=
    (kernel_continuous.mono right_subset).intervalIntegrable_of_Icc
    (by linarith [cutoff_mem.2] : center + cutoff ≤ center + radius)
  have whole_interval : (center - radius) ≤ center + radius := by linarith
  have left_remainder := remainder_integrable.mono_set
    (show uIcc (center - radius) (center - cutoff) ⊆ uIcc (center - radius) (center + radius) from by
      rw [uIcc_of_le (by linarith [cutoff_mem.2]), uIcc_of_le whole_interval]
      exact fun source membership => ⟨membership.1, by linarith [membership.2, cutoff_mem.1]⟩)
  have right_remainder := remainder_integrable.mono_set
    (show uIcc (center + cutoff) (center + radius) ⊆ uIcc (center - radius) (center + radius) from by
      rw [uIcc_of_le (by linarith [cutoff_mem.2]), uIcc_of_le whole_interval]
      exact fun source membership => ⟨by linarith [membership.1, cutoff_mem.1], membership.2⟩)
  have identity : (fun source => density source * kernel source) =
      (fun source => (density source - density center) * kernel source + density center * kernel source) := by
    funext source
    ring
  rw [identity, intervalIntegral.integral_add left_remainder (left_integrable.const_mul _),
    intervalIntegral.integral_add right_remainder (right_integrable.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  ring

theorem contourCauchyTransform_principal_value {curve tangent density : ℝ → ℂ}
    {holder densityHolder difference : ℝ}
    (holder_nonneg : 0 ≤ holder) (densityHolder_nonneg : 0 ≤ densityHolder)
    (difference_nonneg : 0 ≤ difference) (close : difference < 2 / Real.pi)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (density_continuous : Continuous density)
    (derivative : ∀ source : ℝ, HasDerivAt curve (tangent source) source)
    (holder_bound : ∀ first second : ℝ,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (density_holder : ∀ first second : ℝ,
      ‖density first - density second‖ ≤ densityHolder * Real.sqrt |first - second|)
    (derivative_difference : ∀ source : ℝ,
      ‖tangent source - standardCircleTangent source‖ ≤ difference)
    (periodic : Function.Periodic curve (2 * Real.pi)) (label : ℝ) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (label - Real.pi)..(label - cutoff),
        density source * contourCauchyKernel curve tangent label source) +
      ∫ source in (label + cutoff)..(label + Real.pi),
        density source * contourCauchyKernel curve tangent label source)
      (𝓝[>] 0) (𝓝 (contourCauchyTransform curve tangent density label)) := by
  have chord_pos : 0 < 2 / Real.pi - difference := sub_pos.mpr close
  have nearby : ∀ source ∈ Icc (label - Real.pi) (label + Real.pi),
      |source - label| ≤ Real.pi := by
    intro source membership
    rw [abs_le]
    constructor <;> linarith [membership.1, membership.2]
  have chord_bound := fun source membership =>
    contour_near_circle_chord_bound derivative derivative_difference (nearby source membership)
  have tangent_bound : ∀ source : ℝ, ‖tangent source‖ ≤ 1 + difference := by
    intro source
    have estimate := norm_add_le (tangent source - standardCircleTangent source) (standardCircleTangent source)
    rw [sub_add_cancel, standardCircleTangent_norm] at estimate
    linarith [derivative_difference source]
  have remainder_integrable : IntegrableOn (contourCauchyDensityRemainder curve tangent density label)
      (Icc (label - Real.pi) (label + Real.pi)) volume :=
    contourCauchyDensityRemainder_integrable_interval densityHolder_nonneg (by linarith) chord_pos
      curve_continuous tangent_continuous density_continuous
      (fun source _ => density_holder source label) (fun source _ => tangent_bound source) chord_bound
  have remainder_identity : (fun source => (density source - density label) *
      contourCauchyKernel curve tangent label source) =
      contourCauchyDensityRemainder curve tangent density label := by
    funext source
    simp only [contourCauchyKernel, contourCauchyDensityRemainder, mul_div_assoc]
  have kernel_continuous : ContinuousOn (contourCauchyKernel curve tangent label)
      (Icc (label - Real.pi) (label + Real.pi) \ {label}) := by
    apply tangent_continuous.continuousOn.div (continuousOn_const.sub curve_continuous.continuousOn)
    intro source membership
    have distinct : source ≠ label := by simpa only [mem_singleton_iff] using membership.2
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr
      (sub_ne_zero.mpr distinct))).trans_le (chord_bound source membership.1)))
  have result := principal_value_density_subtraction Real.pi_pos kernel_continuous
    ((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.pi_pos] :
      label - Real.pi ≤ label + Real.pi)).mpr (by rwa [remainder_identity]))
    (contourCauchy_near_circle_principal_value_at holder_nonneg difference_nonneg close
      curve_continuous tangent_continuous derivative holder_bound derivative_difference periodic label)
  convert result using 1
  rw [remainder_identity]
  unfold contourCauchyTransform
  congr 1
  ring

end EulerNonuniqueness.Paper
