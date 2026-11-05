import EulerNonuniqueness.Section3.ContourDynamics
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable def inverseSqrtDistance (center source : ℝ) : ℝ :=
  (Real.sqrt |source - center|)⁻¹

theorem inverseSqrtDistance_nonneg (center source : ℝ) :
    0 ≤ inverseSqrtDistance center source := by
  unfold inverseSqrtDistance
  positivity

theorem inverseSqrtDistance_zero_even (source : ℝ) :
    inverseSqrtDistance 0 (-source) = inverseSqrtDistance 0 source := by
  simp [inverseSqrtDistance]

theorem inverseSqrtDistance_integrable_zero_right {radius : ℝ} (radius_pos : 0 < radius) :
    IntervalIntegrable (inverseSqrtDistance 0) volume 0 radius := by
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le radius_pos.le]
  apply ((intervalIntegral.integrableOn_Ioo_rpow_iff radius_pos).2
    (by norm_num : -1 < -(1 / 2 : ℝ))).congr_fun _ measurableSet_Ioo
  intro source membership
  dsimp
  rw [Real.rpow_neg membership.1.le, ← Real.sqrt_eq_rpow]
  simp only [inverseSqrtDistance, sub_zero, abs_of_pos membership.1]

theorem inverseSqrtDistance_integral_zero_right {radius : ℝ} (radius_pos : 0 < radius) :
    (∫ source in (0 : ℝ)..radius, inverseSqrtDistance 0 source) = 2 * Real.sqrt radius := by
  rw [intervalIntegral.integral_of_le radius_pos.le, integral_Ioc_eq_integral_Ioo]
  convert integral_inv_sqrt_Ioo radius_pos using 1
  apply setIntegral_congr_fun measurableSet_Ioo
  intro source membership
  simp [inverseSqrtDistance, abs_of_pos membership.1]

theorem inverseSqrtDistance_integrable_symmetric {radius : ℝ} (radius_pos : 0 < radius) :
    IntervalIntegrable (inverseSqrtDistance 0) volume (-radius) radius := by
  have right := inverseSqrtDistance_integrable_zero_right radius_pos
  have reflected := (IntervalIntegrable.iff_comp_neg.mp right).symm
  have left : IntervalIntegrable (inverseSqrtDistance 0) volume (-radius) 0 := by
    simpa only [neg_zero, inverseSqrtDistance_zero_even] using reflected
  exact left.trans right

theorem inverseSqrtDistance_integral_symmetric {radius : ℝ} (radius_pos : 0 < radius) :
    (∫ source in (-radius)..radius, inverseSqrtDistance 0 source) = 4 * Real.sqrt radius := by
  have integrable := inverseSqrtDistance_integrable_symmetric radius_pos
  have zero_mem : (0 : ℝ) ∈ uIcc (-radius) radius := by
    rw [uIcc_of_le (by linarith)]
    constructor <;> linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integrable.mono_set (uIcc_subset_uIcc_left zero_mem))
    (integrable.mono_set (uIcc_subset_uIcc_right zero_mem))]
  have reflected : (∫ source in (-radius)..0, inverseSqrtDistance 0 source) =
      ∫ source in (0 : ℝ)..radius, inverseSqrtDistance 0 source := by
    simpa only [neg_zero, inverseSqrtDistance_zero_even] using
      (intervalIntegral.integral_comp_neg (inverseSqrtDistance 0) (a := 0) (b := radius)).symm
  rw [reflected, inverseSqrtDistance_integral_zero_right radius_pos]
  ring

theorem inverseSqrtDistance_integrable_centered (center : ℝ) {radius : ℝ} (radius_pos : 0 < radius) :
    IntervalIntegrable (inverseSqrtDistance center) volume (center - radius) (center + radius) := by
  have translated := (inverseSqrtDistance_integrable_symmetric radius_pos).comp_sub_right center
  convert translated using 1
  · funext source
    simp [inverseSqrtDistance]
  · ring
  · ring

theorem inverseSqrtDistance_integral_centered (center : ℝ) {radius : ℝ} (radius_pos : 0 < radius) :
    (∫ source in (center - radius)..(center + radius), inverseSqrtDistance center source) =
      4 * Real.sqrt radius := by
  have translated := intervalIntegral.integral_comp_sub_right (inverseSqrtDistance 0) center
    (a := center - radius) (b := center + radius)
  have identity : (fun source => inverseSqrtDistance 0 (source - center)) =
      inverseSqrtDistance center := by
    funext source
    simp [inverseSqrtDistance]
  rw [identity] at translated
  have lower : center - radius - center = -radius := by ring
  have upper : center + radius - center = radius := by ring
  rw [translated, lower, upper, inverseSqrtDistance_integral_symmetric radius_pos]

theorem measurable_inverseSqrtDistance (center : ℝ) : Measurable (inverseSqrtDistance center) := by
  unfold inverseSqrtDistance
  fun_prop

theorem inverseSqrtDistance_integrable_interval (center lower upper : ℝ) :
    IntervalIntegrable (inverseSqrtDistance center) volume lower upper := by
  let radius := |lower - center| + |upper - center| + 1
  have radius_pos : 0 < radius := by dsimp [radius]; positivity
  have lower_mem : lower ∈ uIcc (center - radius) (center + radius) := by
    rw [uIcc_of_le (by linarith)]
    constructor <;> dsimp [radius] <;>
      linarith [neg_abs_le (lower - center), le_abs_self (lower - center), abs_nonneg (upper - center)]
  have upper_mem : upper ∈ uIcc (center - radius) (center + radius) := by
    rw [uIcc_of_le (by linarith)]
    constructor <;> dsimp [radius] <;>
      linarith [neg_abs_le (upper - center), le_abs_self (upper - center), abs_nonneg (lower - center)]
  exact (inverseSqrtDistance_integrable_centered center radius_pos).mono_set
    (uIcc_subset_uIcc_iff_mem.mpr ⟨lower_mem, upper_mem⟩)

theorem inverseSqrtDistance_setIntegral_centered (center : ℝ) {radius : ℝ} (radius_pos : 0 < radius) :
    (∫ source in Ioo (center - radius) (center + radius), inverseSqrtDistance center source) =
      4 * Real.sqrt radius := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
    inverseSqrtDistance_integral_centered center radius_pos]

theorem norm_setIntegral_weakSingular_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {integrand : ℝ → E} {center radius bound : ℝ}
    {domain : Set ℝ} (radius_pos : 0 < radius) (bound_nonneg : 0 ≤ bound)
    (domain_measurable : MeasurableSet domain)
    (domain_subset : domain ⊆ Ioo (center - radius) (center + radius))
    (majorized : ∀ source ∈ domain, ‖integrand source‖ ≤ bound * inverseSqrtDistance center source) :
    ‖∫ source in domain, integrand source‖ ≤ 4 * bound * Real.sqrt radius := by
  have majorant_integrable : IntegrableOn (fun source => bound * inverseSqrtDistance center source)
      (Ioo (center - radius) (center + radius)) volume := by
    apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).mp
      (inverseSqrtDistance_integrable_centered center radius_pos)).const_mul
  have estimate := norm_integral_le_of_norm_le (majorant_integrable.mono_set domain_subset)
    (show ∀ᵐ source ∂volume.restrict domain,
      ‖integrand source‖ ≤ bound * inverseSqrtDistance center source from by
      filter_upwards [ae_restrict_mem (μ := volume) domain_measurable] with source membership
      exact majorized source membership)
  have monotone := setIntegral_mono_set majorant_integrable
    (show 0 ≤ᵐ[volume.restrict (Ioo (center - radius) (center + radius))]
      (fun source => bound * inverseSqrtDistance center source) from
      Eventually.of_forall (fun source => mul_nonneg bound_nonneg (inverseSqrtDistance_nonneg center source)))
    (Eventually.of_forall domain_subset)
  apply estimate.trans
  convert monotone using 1
  rw [integral_const_mul, inverseSqrtDistance_setIntegral_centered center radius_pos]
  ring

theorem weakSingular_integrable {integrand : ℝ → ℂ} {center lower upper bound : ℝ}
    (measurable : AEStronglyMeasurable integrand (volume.restrict (Icc lower upper)))
    (majorized : ∀ source ∈ Icc lower upper,
      ‖integrand source‖ ≤ bound * inverseSqrtDistance center source) :
    IntegrableOn integrand (Icc lower upper) volume := by
  have majorant_integrable : IntegrableOn (fun source => bound * inverseSqrtDistance center source)
      (Icc lower upper) volume := by
    by_cases ordered : lower ≤ upper
    · exact ((intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp
        (inverseSqrtDistance_integrable_interval center lower upper)).const_mul bound
    · simp only [Icc_eq_empty ordered, integrableOn_empty]
  apply majorant_integrable.mono' measurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with source membership
  exact majorized source membership

theorem inverseSqrtDistance_le_of_separated {center source separation : ℝ}
    (separation_pos : 0 < separation) (separated : separation ≤ |source - center|) :
    inverseSqrtDistance center source ≤ (Real.sqrt separation)⁻¹ := by
  unfold inverseSqrtDistance
  exact inv_anti₀ (Real.sqrt_pos.mpr separation_pos) (Real.sqrt_le_sqrt separated)

theorem weakSingular_far_integral_continuousAt {kernel : ℝ → ℝ → ℂ}
    {target parameterRadius cutoff lower upper bound : ℝ}
    (parameterRadius_pos : 0 < parameterRadius) (cutoff_pos : 0 < cutoff)
    (bound_nonneg : 0 ≤ bound)
    (measurable : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      AEStronglyMeasurable (kernel parameter) (volume.restrict (Icc lower upper)))
    (majorized : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        ‖kernel parameter source‖ ≤ bound * inverseSqrtDistance parameter source)
    (off_diagonal : ∀ source ∈ Icc lower upper, source ≠ target →
      ContinuousAt (fun parameter => kernel parameter source) target) :
    ContinuousAt (fun parameter =>
      ∫ source in Icc lower upper \ Ioo (target - cutoff) (target + cutoff), kernel parameter source) target := by
  let domain := Icc lower upper \ Ioo (target - cutoff) (target + cutoff)
  have domain_measurable : MeasurableSet domain := measurableSet_Icc.diff measurableSet_Ioo
  have finite : volume domain < ⊤ := by
    exact (measure_mono diff_subset).trans_lt (isCompact_Icc.measure_lt_top)
  have near : ∀ᶠ parameter in 𝓝 target,
      parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius) ∧
        |parameter - target| < cutoff / 2 := by
    have radius_neighborhood : Ioo (target - parameterRadius) (target + parameterRadius) ∈ 𝓝 target :=
      Ioo_mem_nhds (by linarith) (by linarith)
    have cutoff_neighborhood : Ioo (target - cutoff / 2) (target + cutoff / 2) ∈ 𝓝 target :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [radius_neighborhood, cutoff_neighborhood] with parameter hr hc
    exact ⟨hr, abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.2]⟩⟩
  apply continuousAt_of_dominated
    (μ := volume.restrict domain) (bound := fun _ => bound * (Real.sqrt (cutoff / 2))⁻¹)
  · filter_upwards [near] with parameter membership
    exact (measurable parameter membership.1).mono_measure (Measure.restrict_mono diff_subset le_rfl)
  · filter_upwards [near] with parameter membership
    filter_upwards [ae_restrict_mem (μ := volume) domain_measurable] with source source_mem
    have far_distance : cutoff ≤ |source - target| := by
      by_contra! h
      apply source_mem.2
      have hs := abs_lt.mp h
      constructor <;> linarith [hs.1, hs.2]
    have triangle : |source - target| ≤ |source - parameter| + |parameter - target| := by
      convert abs_add (source - parameter) (parameter - target) using 1; congr 1; ring
    have separated : cutoff / 2 ≤ |source - parameter| := by linarith
    exact (majorized parameter membership.1 source source_mem.1).trans
      (mul_le_mul_of_nonneg_left
        (inverseSqrtDistance_le_of_separated (by linarith) separated) bound_nonneg)
  · exact integrableOn_const.2 (Or.inr finite)
  · filter_upwards [ae_restrict_mem (μ := volume) domain_measurable] with source source_mem
    apply off_diagonal source source_mem.1
    intro equal
    apply source_mem.2
    rw [equal]
    constructor <;> linarith

theorem weakSingular_integral_continuousAt {kernel : ℝ → ℝ → ℂ}
    {target parameterRadius lower upper bound : ℝ}
    (parameterRadius_pos : 0 < parameterRadius) (bound_nonneg : 0 ≤ bound)
    (measurable : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      AEStronglyMeasurable (kernel parameter) (volume.restrict (Icc lower upper)))
    (majorized : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        ‖kernel parameter source‖ ≤ bound * inverseSqrtDistance parameter source)
    (off_diagonal : ∀ source ∈ Icc lower upper, source ≠ target →
      ContinuousAt (fun parameter => kernel parameter source) target) :
    ContinuousAt (fun parameter => ∫ source in Icc lower upper, kernel parameter source) target := by
  apply Metric.continuousAt_iff.mpr
  intro epsilon epsilon_pos
  let cutoff := (epsilon / (64 * (bound + 1))) ^ 2
  have cutoff_pos : 0 < cutoff := by dsimp [cutoff]; positivity
  have target_mem : target ∈ Ioo (target - parameterRadius) (target + parameterRadius) := by
    constructor <;> linarith
  have cutoff_small : 16 * bound * Real.sqrt cutoff < epsilon / 2 := by
    dsimp [cutoff]
    rw [Real.sqrt_sq (by positivity : 0 ≤ epsilon / (64 * (bound + 1)))]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < 64 * (bound + 1))).mpr
    nlinarith [mul_nonneg bound_nonneg epsilon_pos.le]
  let nearDomain := Icc lower upper ∩ Ioo (target - cutoff) (target + cutoff)
  let nearIntegral := fun parameter => ∫ source in nearDomain, kernel parameter source
  let farIntegral := fun parameter =>
    ∫ source in Icc lower upper \ Ioo (target - cutoff) (target + cutoff), kernel parameter source
  have near_measurable : MeasurableSet nearDomain := measurableSet_Icc.inter measurableSet_Ioo
  have near_bound : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      |parameter - target| < cutoff → ‖nearIntegral parameter‖ ≤ 8 * bound * Real.sqrt cutoff := by
    intro parameter parameter_mem close
    have domain_subset : nearDomain ⊆ Ioo (parameter - 2 * cutoff) (parameter + 2 * cutoff) := by
      intro source membership
      have parameter_bounds := abs_lt.mp close
      constructor <;> linarith [membership.2.1, membership.2.2, parameter_bounds.1, parameter_bounds.2]
    have estimate := norm_setIntegral_weakSingular_near (center := parameter)
      (radius := 2 * cutoff) (by positivity) bound_nonneg near_measurable domain_subset
      (fun source membership => majorized parameter parameter_mem source membership.1)
    have sqrt_bound : Real.sqrt (2 * cutoff) ≤ 2 * Real.sqrt cutoff := by
      nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * cutoff), Real.sq_sqrt cutoff_pos.le,
        Real.sqrt_nonneg (2 * cutoff), Real.sqrt_nonneg cutoff]
    apply estimate.trans
    calc
      _ ≤ 4 * bound * (2 * Real.sqrt cutoff) := mul_le_mul_of_nonneg_left sqrt_bound (by positivity)
      _ = _ := by ring
  have far_continuous : ContinuousAt farIntegral target :=
    weakSingular_far_integral_continuousAt parameterRadius_pos cutoff_pos bound_nonneg
      measurable majorized off_diagonal
  obtain ⟨delta, delta_pos, far_close⟩ := Metric.continuousAt_iff.mp far_continuous
    (epsilon / 2) (by positivity)
  refine ⟨min parameterRadius (min cutoff delta), by positivity, ?_⟩
  intro parameter close
  have parameter_close : |parameter - target| < parameterRadius := by
    exact (show |parameter - target| < min parameterRadius (min cutoff delta) from
      by simpa only [Real.dist_eq] using close).trans_le (min_le_left _ _)
  have cutoff_close : |parameter - target| < cutoff := by
    exact (show |parameter - target| < min parameterRadius (min cutoff delta) from
      by simpa only [Real.dist_eq] using close).trans_le
        ((min_le_right _ _).trans (min_le_left _ _))
  have delta_close : dist parameter target < delta :=
    close.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have parameter_mem : parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius) := by
    have bounds := abs_lt.mp parameter_close
    constructor <;> linarith [bounds.1, bounds.2]
  have decomposition : ∀ current ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      (∫ source in Icc lower upper, kernel current source) = nearIntegral current + farIntegral current := by
    intro current membership
    exact (integral_inter_add_diff measurableSet_Ioo
      (weakSingular_integrable (measurable current membership) (majorized current membership))).symm
  have difference :
      (∫ source in Icc lower upper, kernel parameter source) -
        (∫ source in Icc lower upper, kernel target source) =
      nearIntegral parameter + (farIntegral parameter - farIntegral target) - nearIntegral target := by
    rw [decomposition parameter parameter_mem, decomposition target target_mem]
    abel
  rw [dist_eq_norm, difference]
  calc
    _ ≤ ‖nearIntegral parameter + (farIntegral parameter - farIntegral target)‖ + ‖nearIntegral target‖ :=
      norm_sub_le _ _
    _ ≤ ‖nearIntegral parameter‖ + ‖farIntegral parameter - farIntegral target‖ + ‖nearIntegral target‖ :=
      add_le_add_right (norm_add_le _ _) _
    _ < epsilon := by
      have near_current := near_bound parameter parameter_mem cutoff_close
      have near_target := near_bound target target_mem (by simpa using cutoff_pos)
      have far := far_close delta_close
      rw [dist_eq_norm] at far
      linarith

theorem contourChordPhaseDerivative_integral_continuousAt {curve tangent : ℝ → ℂ}
    {target parameterRadius lower upper holder speed chord : ℝ}
    (parameterRadius_pos : 0 < parameterRadius)
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (lower_bound : lower ≤ target - parameterRadius) (upper_bound : target + parameterRadius ≤ upper)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc lower upper))
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        chord * |parameter - source| ≤ ‖curve parameter - curve source‖) :
    ContinuousAt (fun parameter => ∫ source in Icc lower upper,
      contourChordPhaseDerivative curve tangent parameter source * star (tangent source)) target := by
  have ordered : lower ≤ upper := by linarith
  have target_mem : target ∈ Ioo lower upper := by constructor <;> linarith
  have parameter_mem : ∀ parameter ∈ Ioo (target - parameterRadius) (target + parameterRadius),
      parameter ∈ Icc lower upper := by
    intro parameter membership
    exact ⟨lower_bound.trans membership.1.le, membership.2.le.trans upper_bound⟩
  have curve_continuous : ContinuousOn curve (Icc lower upper) :=
    fun x hx => (derivative x hx).continuousAt.continuousWithinAt
  have curve_measurable := curve_continuous.aestronglyMeasurable (μ := volume) measurableSet_Icc
  have tangent_measurable := tangent_continuous.aestronglyMeasurable (μ := volume) measurableSet_Icc
  apply weakSingular_integral_continuousAt parameterRadius_pos
    (bound := 2 * speed ^ 2 * holder / chord ^ 2) (by positivity)
  · intro parameter membership
    have difference_measurable : AEMeasurable (fun source => curve parameter - curve source)
        (volume.restrict (Icc lower upper)) := aemeasurable_const.sub curve_measurable.aemeasurable
    have conjugate_measurable : AEMeasurable (fun source => star (curve parameter - curve source))
        (volume.restrict (Icc lower upper)) :=
      continuous_star.measurable.comp_aemeasurable difference_measurable
    have numerator_measurable : AEMeasurable (fun source =>
        tangent parameter * star (curve parameter - curve source) -
          (curve parameter - curve source) * star (tangent parameter))
        (volume.restrict (Icc lower upper)) :=
      (aemeasurable_const.mul conjugate_measurable).sub (difference_measurable.mul aemeasurable_const)
    have star_tangent_measurable : AEMeasurable (fun source => star (tangent source))
        (volume.restrict (Icc lower upper)) :=
      continuous_star.measurable.comp_aemeasurable tangent_measurable.aemeasurable
    exact ((numerator_measurable.div (conjugate_measurable.pow_const 2)).mul
      star_tangent_measurable).aestronglyMeasurable
  · intro parameter membership source source_mem
    by_cases equal : parameter = source
    · subst parameter
      simp [contourChordPhaseDerivative, inverseSqrtDistance]
    have interval_subset : uIcc source parameter ⊆ Icc lower upper := by
      have subset := uIcc_subset_uIcc_iff_mem.mpr
        ⟨show source ∈ uIcc lower upper by simpa only [uIcc_of_le ordered] using source_mem,
          show parameter ∈ uIcc lower upper by
            simpa only [uIcc_of_le ordered] using parameter_mem parameter membership⟩
      simpa only [uIcc_of_le ordered] using subset
    have bound := contourChordPhaseDerivative_bound equal holder_nonneg speed_nonneg chord_pos
      (fun x hx => derivative x (interval_subset hx))
      (fun x hx => holder_bound x (interval_subset hx) parameter (parameter_mem parameter membership))
      (tangent_bound parameter (parameter_mem parameter membership))
      (chord_bound parameter membership source source_mem)
    rw [norm_mul, norm_star]
    calc
      _ ≤ ((2 * speed * holder / chord ^ 2) / Real.sqrt |parameter - source|) * speed :=
        mul_le_mul bound (tangent_bound source source_mem) (norm_nonneg _) (by positivity)
      _ = _ := by simp only [inverseSqrtDistance, abs_sub_comm parameter source]; ring
  · intro source source_mem distinct
    have curve_at : ContinuousAt curve target := (derivative target ⟨target_mem.1.le, target_mem.2.le⟩).continuousAt
    have tangent_at : ContinuousAt tangent target :=
      (tangent_continuous target ⟨target_mem.1.le, target_mem.2.le⟩).continuousAt (Icc_mem_nhds target_mem.1 target_mem.2)
    have separated : curve target - curve source ≠ 0 := by
      apply norm_ne_zero_iff.mp
      have distance_pos : 0 < |target - source| := abs_pos.mpr (sub_ne_zero.mpr distinct.symm)
      exact (ne_of_gt ((mul_pos chord_pos distance_pos).trans_le
        (chord_bound target ⟨by linarith, by linarith⟩ source source_mem)))
    have denominator_ne : star (curve target - curve source) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (star_ne_zero.mpr separated)
    exact (((tangent_at.mul (curve_at.sub_const (curve source)).star).sub
      ((curve_at.sub_const (curve source)).mul tangent_at.star)).div
        ((curve_at.sub_const (curve source)).star.pow 2) denominator_ne).mul continuousAt_const

theorem integral_eq_sub_of_hasDerivAt_except_point {function derivative : ℝ → ℂ}
    {lower upper singular : ℝ} (ordered : lower ≤ upper)
    (continuous : ContinuousOn function (Icc lower upper))
    (differentiable : ∀ x ∈ Ioo lower upper, x ≠ singular → HasDerivAt function (derivative x) x)
    (integrable : IntervalIntegrable derivative volume lower upper) :
    (∫ x in lower..upper, derivative x) = function upper - function lower := by
  by_cases lower_lt : lower < singular
  · by_cases upper_gt : singular < upper
    · have singular_mem : singular ∈ uIcc lower upper := by
        rw [uIcc_of_le ordered]
        exact ⟨lower_lt.le, upper_gt.le⟩
      have left_integrable := integrable.mono_set (uIcc_subset_uIcc_left singular_mem)
      have right_integrable := integrable.mono_set (uIcc_subset_uIcc_right singular_mem)
      have left := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le lower_lt.le
        (continuous.mono (Icc_subset_Icc le_rfl upper_gt.le))
        (fun x hx => differentiable x ⟨hx.1, hx.2.trans upper_gt⟩ hx.2.ne) left_integrable
      have right := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le upper_gt.le
        (continuous.mono (Icc_subset_Icc lower_lt.le le_rfl))
        (fun x hx => differentiable x ⟨lower_lt.trans hx.1, hx.2⟩ hx.1.ne') right_integrable
      rw [← intervalIntegral.integral_add_adjacent_intervals left_integrable right_integrable, left, right]
      abel
    · apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered continuous _ integrable
      intro x hx
      apply differentiable x hx
      intro equal
      linarith [hx.2]
  · apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ordered continuous _ integrable
    intro x hx
    apply differentiable x hx
    intro equal
    linarith [hx.1]

noncomputable def contourChordPhaseExtension (curve : ℝ → ℂ) (target source : ℝ) : ℂ :=
  dslope curve source target / star (dslope curve source target)

theorem contourChordPhaseExtension_of_ne (curve : ℝ → ℂ) {target source : ℝ}
    (distinct : target ≠ source) :
    contourChordPhaseExtension curve target source = contourChordPhase curve target source := by
  unfold contourChordPhaseExtension contourChordPhase
  rw [dslope_of_ne curve distinct, slope_def_module]
  simp only [star_smul, star_trivial, Complex.real_smul]
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm ((starRingEnd ℂ) (curve target - curve source))]
  apply mul_div_mul_left
  have real_ne : (target - source)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr distinct)
  exact_mod_cast real_ne

theorem contourChordPhaseExtension_continuousAt_diagonal {curve : ℝ → ℂ}
    {source : ℝ} {tangent : ℂ} (derivative : HasDerivAt curve tangent source) (nonzero : tangent ≠ 0) :
    ContinuousAt (fun target => contourChordPhaseExtension curve target source) source := by
  have slope_continuous : ContinuousAt (dslope curve source) source :=
    continuousAt_dslope_same.mpr derivative.differentiableAt
  apply slope_continuous.div slope_continuous.star
  rw [dslope_same, derivative.deriv]
  exact star_ne_zero.mpr nonzero

theorem contourChordPhaseExtension_derivative {curve tangent : ℝ → ℂ} {target source : ℝ}
    (distinct : target ≠ source) (derivative : HasDerivAt curve (tangent target) target)
    (separated : curve target - curve source ≠ 0) :
    HasDerivAt (fun current => contourChordPhaseExtension curve current source)
      (contourChordPhaseDerivative curve tangent target source) target := by
  have eventually_equal : (fun current => contourChordPhaseExtension curve current source) =ᶠ[𝓝 target]
      (fun current => contourChordPhase curve current source) := by
    filter_upwards [isOpen_ne.mem_nhds distinct] with current membership
    exact contourChordPhaseExtension_of_ne curve membership
  exact (contourChordPhase_derivative derivative separated).congr_of_eventuallyEq eventually_equal

theorem weakSingular_integrable_prod {kernel : ℝ → ℝ → ℂ}
    {parameterLower parameterUpper sourceLower sourceUpper bound : ℝ}
    (bound_nonneg : 0 ≤ bound)
    (measurable : AEStronglyMeasurable (Function.uncurry kernel)
      ((volume.restrict (Icc parameterLower parameterUpper)).prod
        (volume.restrict (Icc sourceLower sourceUpper))))
    (majorized : ∀ parameter ∈ Icc parameterLower parameterUpper,
      ∀ source ∈ Icc sourceLower sourceUpper,
        ‖kernel parameter source‖ ≤ bound * inverseSqrtDistance parameter source) :
    Integrable (Function.uncurry kernel)
      ((volume.restrict (Icc parameterLower parameterUpper)).prod
        (volume.restrict (Icc sourceLower sourceUpper))) := by
  let radius := |parameterLower| + |parameterUpper| + |sourceLower| + |sourceUpper| + 1
  have radius_pos : 0 < radius := by dsimp [radius]; positivity
  have domain_subset : ∀ parameter ∈ Icc parameterLower parameterUpper,
      Icc sourceLower sourceUpper ⊆ Ioo (parameter - radius) (parameter + radius) := by
    intro parameter parameter_mem source source_mem
    have parameter_abs : |parameter| ≤ |parameterLower| + |parameterUpper| := by
      apply abs_le.mpr
      constructor <;> linarith [parameter_mem.1, parameter_mem.2,
        neg_abs_le parameterLower, le_abs_self parameterUpper,
        abs_nonneg parameterLower, abs_nonneg parameterUpper]
    have source_abs : |source| ≤ |sourceLower| + |sourceUpper| := by
      apply abs_le.mpr
      constructor <;> linarith [source_mem.1, source_mem.2,
        neg_abs_le sourceLower, le_abs_self sourceUpper,
        abs_nonneg sourceLower, abs_nonneg sourceUpper]
    have distance : |source - parameter| < radius := by
      calc
        _ ≤ |source| + |parameter| := abs_sub source parameter
        _ < _ := by dsimp [radius]; linarith
    have bounds := abs_lt.mp distance
    constructor <;> linarith [bounds.1, bounds.2]
  apply (integrable_prod_iff measurable).mpr
  constructor
  · filter_upwards [measurable.prodMk_left,
      ae_restrict_mem (μ := volume) measurableSet_Icc] with parameter parameter_measurable parameter_mem
    exact weakSingular_integrable parameter_measurable (majorized parameter parameter_mem)
  · have majorant_integrable : Integrable (fun _ : ℝ => 4 * bound * Real.sqrt radius)
        (volume.restrict (Icc parameterLower parameterUpper)) :=
      integrableOn_const.2 (Or.inr isCompact_Icc.measure_lt_top)
    apply majorant_integrable.mono' measurable.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with parameter parameter_mem
    exact norm_setIntegral_weakSingular_near radius_pos bound_nonneg measurableSet_Icc
      (domain_subset parameter parameter_mem)
      (fun source source_mem => by simpa only [Real.norm_eq_abs, abs_norm] using
        (majorized parameter parameter_mem source source_mem))

theorem integral_eq_sub_of_hasDerivAt_except_point_unordered {function derivative : ℝ → ℂ}
    {first last singular : ℝ}
    (continuous : ContinuousOn function (uIcc first last))
    (differentiable : ∀ x ∈ Ioo (min first last) (max first last), x ≠ singular →
      HasDerivAt function (derivative x) x)
    (integrable : IntervalIntegrable derivative volume first last) :
    (∫ x in first..last, derivative x) = function last - function first := by
  rcases le_total first last with ordered | ordered
  · apply integral_eq_sub_of_hasDerivAt_except_point ordered
      (by simpa only [uIcc_of_le ordered] using continuous)
      (by simpa only [min_eq_left ordered, max_eq_right ordered] using differentiable) integrable
  · rw [intervalIntegral.integral_symm]
    have identity := integral_eq_sub_of_hasDerivAt_except_point ordered
      (by simpa only [uIcc_of_ge ordered] using continuous)
      (by simpa only [min_eq_right ordered, max_eq_left ordered] using differentiable) integrable.symm
    rw [identity]
    abel

theorem setIntegral_intervalIntegral_swap {kernel : ℝ → ℝ → ℂ}
    {first last sourceLower sourceUpper : ℝ}
    (integrable : Integrable (Function.uncurry kernel)
      ((volume.restrict (uIoc first last)).prod (volume.restrict (Icc sourceLower sourceUpper)))) :
    (∫ source in Icc sourceLower sourceUpper, ∫ parameter in first..last, kernel parameter source) =
      ∫ parameter in first..last, ∫ source in Icc sourceLower sourceUpper, kernel parameter source := by
  have swap := integral_integral_swap integrable
  rcases le_total first last with ordered | ordered
  · rw [uIoc_of_le ordered] at swap
    simpa only [intervalIntegral.integral_of_le ordered] using swap.symm
  · rw [uIoc_of_ge ordered] at swap
    simp only [intervalIntegral.integral_of_ge ordered, integral_neg]
    exact congrArg Neg.neg swap.symm

theorem hasDerivAt_setIntegral_via_continuous_derivative_integral
    {primitive derivative : ℝ → ℝ → ℂ} {target parameterLower parameterUpper sourceLower sourceUpper : ℝ}
    (target_mem : target ∈ Ioo parameterLower parameterUpper)
    (primitive_integrable : ∀ parameter ∈ Icc parameterLower parameterUpper,
      IntegrableOn (primitive parameter) (Icc sourceLower sourceUpper) volume)
    (primitive_continuous : ∀ source ∈ Icc sourceLower sourceUpper,
      ContinuousOn (fun parameter => primitive parameter source) (Icc parameterLower parameterUpper))
    (primitive_derivative : ∀ source ∈ Icc sourceLower sourceUpper,
      ∀ parameter ∈ Icc parameterLower parameterUpper, parameter ≠ source →
        HasDerivAt (fun current => primitive current source) (derivative parameter source) parameter)
    (derivative_integrable : Integrable (Function.uncurry derivative)
      ((volume.restrict (Icc parameterLower parameterUpper)).prod
        (volume.restrict (Icc sourceLower sourceUpper))))
    (derivative_integral_continuous : ContinuousAt
      (fun parameter => ∫ source in Icc sourceLower sourceUpper, derivative parameter source) target) :
    HasDerivAt (fun parameter => ∫ source in Icc sourceLower sourceUpper, primitive parameter source)
      (∫ source in Icc sourceLower sourceUpper, derivative target source) target := by
  have ordered : parameterLower ≤ parameterUpper := target_mem.1.le.trans target_mem.2.le
  have target_closed : target ∈ Icc parameterLower parameterUpper := ⟨target_mem.1.le, target_mem.2.le⟩
  have identity : ∀ parameter ∈ Icc parameterLower parameterUpper,
      (∫ source in Icc sourceLower sourceUpper, primitive parameter source) =
        (∫ source in Icc sourceLower sourceUpper, primitive target source) +
          ∫ current in target..parameter,
            ∫ source in Icc sourceLower sourceUpper, derivative current source := by
    intro parameter parameter_mem
    have interval_subset : uIcc target parameter ⊆ Icc parameterLower parameterUpper := by
      have subset := uIcc_subset_uIcc_iff_mem.mpr
        ⟨show target ∈ uIcc parameterLower parameterUpper by
            simpa only [uIcc_of_le ordered] using target_closed,
          show parameter ∈ uIcc parameterLower parameterUpper by
            simpa only [uIcc_of_le ordered] using parameter_mem⟩
      simpa only [uIcc_of_le ordered] using subset
    have source_identity : ∀ᵐ source ∂volume.restrict (Icc sourceLower sourceUpper),
        (∫ current in target..parameter, derivative current source) =
          primitive parameter source - primitive target source := by
      filter_upwards [derivative_integrable.prod_left_ae,
        ae_restrict_mem (μ := volume) measurableSet_Icc] with source source_integrable source_mem
      have full_interval_integrable : IntervalIntegrable (fun current => derivative current source)
          volume parameterLower parameterUpper :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr source_integrable
      apply integral_eq_sub_of_hasDerivAt_except_point_unordered (singular := source)
        ((primitive_continuous source source_mem).mono interval_subset) _
        (full_interval_integrable.mono_set (by simpa only [uIcc_of_le ordered] using interval_subset))
      intro current current_mem distinct
      apply primitive_derivative source source_mem current _ distinct
      apply interval_subset
      exact ⟨current_mem.1.le, current_mem.2.le⟩
    have subinterval_integrable : Integrable (Function.uncurry derivative)
        ((volume.restrict (uIoc target parameter)).prod
          (volume.restrict (Icc sourceLower sourceUpper))) := by
      rw [Measure.prod_restrict] at derivative_integrable ⊢
      exact derivative_integrable.mono_measure
        (Measure.restrict_mono (Set.prod_mono (uIoc_subset_uIcc.trans interval_subset) Subset.rfl) le_rfl)
    have difference_identity :
        (∫ source in Icc sourceLower sourceUpper, primitive parameter source) -
          (∫ source in Icc sourceLower sourceUpper, primitive target source) =
        ∫ current in target..parameter,
          ∫ source in Icc sourceLower sourceUpper, derivative current source := by
      rw [← integral_sub (primitive_integrable parameter parameter_mem) (primitive_integrable target target_closed)]
      calc
        _ = ∫ source in Icc sourceLower sourceUpper,
            ∫ current in target..parameter, derivative current source :=
          integral_congr_ae (source_identity.mono (fun source identity => identity.symm))
        _ = _ := setIntegral_intervalIntegral_swap subinterval_integrable
    calc
      _ = ((∫ source in Icc sourceLower sourceUpper, primitive parameter source) -
          (∫ source in Icc sourceLower sourceUpper, primitive target source)) +
          (∫ source in Icc sourceLower sourceUpper, primitive target source) := by abel
      _ = _ := by rw [difference_identity]; abel
  have derivative_measurable : StronglyMeasurableAtFilter
      (fun parameter => ∫ source in Icc sourceLower sourceUpper, derivative parameter source)
      (𝓝 target) volume :=
    ⟨Icc parameterLower parameterUpper, Icc_mem_nhds target_mem.1 target_mem.2,
      derivative_integrable.integral_prod_left.aestronglyMeasurable⟩
  have primitive_hasDerivAt := (intervalIntegral.integral_hasDerivAt_right
    (show IntervalIntegrable
      (fun parameter => ∫ source in Icc sourceLower sourceUpper, derivative parameter source)
        volume target target from by simp) derivative_measurable derivative_integral_continuous).const_add
          (∫ source in Icc sourceLower sourceUpper, primitive target source)
  apply primitive_hasDerivAt.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds target_mem.1 target_mem.2] with parameter parameter_mem
  exact identity parameter ⟨parameter_mem.1.le, parameter_mem.2.le⟩

theorem contourChordPhase_norm_le_one (curve : ℝ → ℂ) (target source : ℝ) :
    ‖contourChordPhase curve target source‖ ≤ 1 := by
  simp only [contourChordPhase, norm_div, norm_star]
  exact div_self_le_one _

theorem contourChordPhaseExtension_integral_eq (curve tangent : ℝ → ℂ)
    (target lower upper : ℝ) :
    (∫ source in Icc lower upper, contourChordPhaseExtension curve target source * star (tangent source)) =
      ∫ source in Icc lower upper, contourChordPhase curve target source * star (tangent source) := by
  apply integral_congr_ae
  have nonzero : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_of_ae nonzero] with source distinct
  rw [contourChordPhaseExtension_of_ne curve distinct.symm]

theorem contourChordPhaseExtension_integrable {curve tangent : ℝ → ℂ}
    {target lower upper speed : ℝ} (curve_continuous : Continuous curve)
    (tangent_continuous : Continuous tangent)
    (tangent_bound : ∀ source ∈ Icc lower upper, ‖tangent source‖ ≤ speed) :
    IntegrableOn (fun source => contourChordPhaseExtension curve target source * star (tangent source))
      (Icc lower upper) volume := by
  have difference_measurable : Measurable (fun source => curve target - curve source) :=
    measurable_const.sub curve_continuous.measurable
  have phase_measurable : Measurable
      (fun source => contourChordPhase curve target source * star (tangent source)) :=
    (difference_measurable.div (continuous_star.measurable.comp difference_measurable)).mul
      (continuous_star.measurable.comp tangent_continuous.measurable)
  have phase_integrable : IntegrableOn
      (fun source => contourChordPhase curve target source * star (tangent source))
      (Icc lower upper) volume := by
    apply (integrableOn_const.2 (Or.inr isCompact_Icc.measure_lt_top) :
      IntegrableOn (fun _ : ℝ => speed) (Icc lower upper) volume).mono'
        phase_measurable.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc] with source source_mem
    rw [norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (contourChordPhase_norm_le_one curve target source)
      (norm_nonneg _)).trans (by simpa only [one_mul] using tangent_bound source source_mem)
  have nonzero : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  apply phase_integrable.congr
  filter_upwards [ae_restrict_of_ae nonzero] with source distinct
  rw [contourChordPhaseExtension_of_ne curve distinct.symm]

theorem measurable_contourChordPhaseDerivative {curve tangent : ℝ → ℂ}
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent) :
    Measurable (fun point : ℝ × ℝ =>
      contourChordPhaseDerivative curve tangent point.1 point.2 * star (tangent point.2)) := by
  have difference : Measurable (fun point : ℝ × ℝ => curve point.1 - curve point.2) :=
    (curve_continuous.measurable.comp measurable_fst).sub (curve_continuous.measurable.comp measurable_snd)
  have first_tangent : Measurable (fun point : ℝ × ℝ => tangent point.1) :=
    tangent_continuous.measurable.comp measurable_fst
  have second_tangent : Measurable (fun point : ℝ × ℝ => tangent point.2) :=
    tangent_continuous.measurable.comp measurable_snd
  have star_difference := continuous_star.measurable.comp difference
  exact (((first_tangent.mul star_difference).sub
    (difference.mul (continuous_star.measurable.comp first_tangent))).div
      (star_difference.pow_const 2)).mul (continuous_star.measurable.comp second_tangent)

theorem contourChordPhaseDerivative_integrand_bound {curve tangent : ℝ → ℂ}
    {parameter source lower upper holder speed chord : ℝ}
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (parameter_mem : parameter ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : chord * |parameter - source| ≤ ‖curve parameter - curve source‖) :
    ‖contourChordPhaseDerivative curve tangent parameter source * star (tangent source)‖ ≤
      (2 * speed ^ 2 * holder / chord ^ 2) * inverseSqrtDistance parameter source := by
  by_cases equal : parameter = source
  · subst parameter
    simp [contourChordPhaseDerivative, inverseSqrtDistance]
  have ordered := parameter_mem.1.trans parameter_mem.2
  have interval_subset : uIcc source parameter ⊆ Icc lower upper := by
    have subset := uIcc_subset_uIcc_iff_mem.mpr
      ⟨show source ∈ uIcc lower upper by simpa only [uIcc_of_le ordered] using source_mem,
        show parameter ∈ uIcc lower upper by simpa only [uIcc_of_le ordered] using parameter_mem⟩
    simpa only [uIcc_of_le ordered] using subset
  have bound := contourChordPhaseDerivative_bound equal holder_nonneg speed_nonneg chord_pos
    (fun x hx => derivative x (interval_subset hx))
    (fun x hx => holder_bound x (interval_subset hx) parameter parameter_mem)
    (tangent_bound parameter parameter_mem) chord_bound
  rw [norm_mul, norm_star]
  calc
    _ ≤ ((2 * speed * holder / chord ^ 2) / Real.sqrt |parameter - source|) * speed :=
      mul_le_mul bound (tangent_bound source source_mem) (norm_nonneg _) (by positivity)
    _ = _ := by simp only [inverseSqrtDistance, abs_sub_comm parameter source]; ring

theorem hasDerivAt_contourChordPhase_integral {curve tangent : ℝ → ℂ}
    {target parameterRadius lower upper holder speed chord : ℝ}
    (parameterRadius_pos : 0 < parameterRadius)
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (lower_bound : lower ≤ target - parameterRadius) (upper_bound : target + parameterRadius ≤ upper)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_nonzero : ∀ x ∈ Icc lower upper, tangent x ≠ 0)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : ∀ parameter ∈ Icc (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        chord * |parameter - source| ≤ ‖curve parameter - curve source‖) :
    HasDerivAt (fun parameter => ∫ source in Icc lower upper,
      contourChordPhase curve parameter source * star (tangent source))
      (∫ source in Icc lower upper,
        contourChordPhaseDerivative curve tangent target source * star (tangent source)) target := by
  have parameter_mem : ∀ parameter ∈ Icc (target - parameterRadius) (target + parameterRadius),
      parameter ∈ Icc lower upper := by
    intro parameter membership
    exact ⟨lower_bound.trans membership.1, membership.2.trans upper_bound⟩
  have separated : ∀ parameter ∈ Icc (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper, parameter ≠ source → curve parameter - curve source ≠ 0 := by
    intro parameter membership source source_mem distinct
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
      (chord_bound parameter membership source source_mem)))
  have result : HasDerivAt (fun parameter => ∫ source in Icc lower upper,
      contourChordPhaseExtension curve parameter source * star (tangent source))
      (∫ source in Icc lower upper,
        contourChordPhaseDerivative curve tangent target source * star (tangent source)) target := by
    apply hasDerivAt_setIntegral_via_continuous_derivative_integral
      (primitive := fun parameter source =>
        contourChordPhaseExtension curve parameter source * star (tangent source))
      (derivative := fun parameter source =>
        contourChordPhaseDerivative curve tangent parameter source * star (tangent source))
      (target := target) (sourceLower := lower) (sourceUpper := upper)
      (parameterLower := target - parameterRadius) (parameterUpper := target + parameterRadius)
      (by constructor <;> linarith)
    · intro parameter membership
      exact contourChordPhaseExtension_integrable curve_continuous tangent_continuous tangent_bound
    · intro source source_mem parameter membership
      apply ContinuousAt.continuousWithinAt
      apply ContinuousAt.mul _ continuousAt_const
      by_cases equal : parameter = source
      · subst parameter
        exact contourChordPhaseExtension_continuousAt_diagonal
          (derivative source source_mem) (tangent_nonzero source source_mem)
      · exact (contourChordPhaseExtension_derivative equal
          (derivative parameter (parameter_mem parameter membership))
          (separated parameter membership source source_mem equal)).continuousAt
    · intro source source_mem parameter membership distinct
      exact (contourChordPhaseExtension_derivative distinct
        (derivative parameter (parameter_mem parameter membership))
        (separated parameter membership source source_mem distinct)).mul_const (star (tangent source))
    · apply weakSingular_integrable_prod
        (kernel := fun parameter source =>
          contourChordPhaseDerivative curve tangent parameter source * star (tangent source))
        (bound := 2 * speed ^ 2 * holder / chord ^ 2) (by positivity)
        (measurable_contourChordPhaseDerivative curve_continuous tangent_continuous).aestronglyMeasurable
      intro parameter membership source source_mem
      exact contourChordPhaseDerivative_integrand_bound holder_nonneg speed_nonneg chord_pos
        (parameter_mem parameter membership) source_mem derivative tangent_bound holder_bound
        (chord_bound parameter membership source source_mem)
    · exact contourChordPhaseDerivative_integral_continuousAt parameterRadius_pos holder_nonneg
        speed_nonneg chord_pos lower_bound upper_bound derivative tangent_continuous.continuousOn
        tangent_bound holder_bound (fun parameter membership source source_mem =>
          chord_bound parameter ⟨membership.1.le, membership.2.le⟩ source source_mem)
  simpa only [contourChordPhaseExtension_integral_eq] using result

theorem contour_speed_bound_on_interval {curve tangent : ℝ → ℂ}
    {lower upper target source speed : ℝ}
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper) :
    ‖curve source - curve target‖ ≤ speed * |source - target| := by
  have estimate := (convex_Icc lower upper).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (derivative x hx).hasDerivWithinAt) tangent_bound target_mem source_mem
  simpa only [Real.norm_eq_abs] using estimate

theorem abs_log_norm_le_of_two_sided_bound {position : ℂ} {distance chord speed : ℝ}
    (distance_pos : 0 < distance) (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (lower_bound : chord * distance ≤ ‖position‖) (upper_bound : ‖position‖ ≤ speed * distance) :
    |Real.log ‖position‖| ≤ |Real.log distance| + |Real.log chord| + |Real.log speed| := by
  have positive := (mul_pos chord_pos distance_pos).trans_le lower_bound
  have lower := Real.log_le_log (mul_pos chord_pos distance_pos) lower_bound
  have upper := Real.log_le_log positive upper_bound
  rw [Real.log_mul chord_pos.ne' distance_pos.ne'] at lower
  rw [Real.log_mul speed_pos.ne' distance_pos.ne'] at upper
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log distance), neg_abs_le (Real.log chord), abs_nonneg (Real.log speed)]
  · linarith [le_abs_self (Real.log distance), le_abs_self (Real.log speed), abs_nonneg (Real.log chord)]

theorem contour_log_integrable_interval {curve tangent : ℝ → ℂ}
    {lower upper target speed chord : ℝ} (ordered : lower ≤ upper)
    (target_mem : target ∈ Icc lower upper) (speed_pos : 0 < speed) (chord_pos : 0 < chord)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ source ∈ Icc lower upper,
      chord * |source - target| ≤ ‖curve source - curve target‖) :
    IntervalIntegrable (fun source => Real.log ‖curve source - curve target‖ • tangent source)
      volume lower upper := by
  have shifted_log : IntervalIntegrable (fun source => Real.log (source - target)) volume lower upper := by
    have base : IntervalIntegrable Real.log volume (lower - target) (upper - target) :=
      intervalIntegral.intervalIntegrable_log'
    simpa only [sub_add_cancel] using base.comp_sub_right target
  have constant_integrable : ∀ value : ℝ, IntegrableOn (fun _ : ℝ => value) (Icc lower upper) volume :=
    fun value => integrableOn_const.2 (Or.inr isCompact_Icc.measure_lt_top)
  have majorant_integrable : IntegrableOn (fun source =>
      (|Real.log (source - target)| + |Real.log chord| + |Real.log speed|) * speed)
      (Icc lower upper) volume := by
    exact ((((intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp shifted_log.norm).add
      (constant_integrable _)).add (constant_integrable _)).mul_const speed
  have measurable : Measurable (fun source => Real.log ‖curve source - curve target‖ • tangent source) :=
    ((curve_continuous.measurable.sub_const (curve target)).norm.log).smul tangent_continuous.measurable
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le ordered]
  apply majorant_integrable.mono' measurable.aestronglyMeasurable.restrict
  have nonzero : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc,
    ae_restrict_of_ae nonzero] with source source_mem distinct
  rw [norm_smul, Real.norm_eq_abs]
  apply mul_le_mul _ (tangent_bound source source_mem) (norm_nonneg _) (by positivity)
  have estimate := abs_log_norm_le_of_two_sided_bound (abs_pos.mpr (sub_ne_zero.mpr distinct))
    chord_pos speed_pos (chord_bound source source_mem)
    (contour_speed_bound_on_interval derivative tangent_bound target_mem source_mem)
  simpa only [Real.log_abs] using estimate

theorem contourChordPhase_swap (curve : ℝ → ℂ) (first second : ℝ) :
    contourChordPhase curve first second = contourChordPhase curve second first := by
  unfold contourChordPhase
  have difference : curve first - curve second = -(curve second - curve first) := by abel
  rw [difference, star_neg]
  exact neg_div_neg_eq _ _

theorem contourChordPhase_integrable {curve tangent : ℝ → ℂ} {target lower upper speed : ℝ}
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (tangent_bound : ∀ source ∈ Icc lower upper, ‖tangent source‖ ≤ speed) :
    IntegrableOn (fun source => contourChordPhase curve target source * star (tangent source))
      (Icc lower upper) volume := by
  apply (contourChordPhaseExtension_integrable (target := target)
    curve_continuous tangent_continuous tangent_bound).congr
  have nonzero : ∀ᵐ source : ℝ ∂volume, source ≠ target := by
    simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
  filter_upwards [ae_restrict_of_ae nonzero] with source distinct
  rw [contourChordPhaseExtension_of_ne curve distinct.symm]

theorem contourVelocity_eq_phase_integral_general {curve tangent : ℝ → ℂ}
    {target lower upper speed chord : ℝ} (target_mem : target ∈ Ioo lower upper)
    (speed_pos : 0 < speed) (chord_pos : 0 < chord)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ source ∈ Icc lower upper,
      chord * |source - target| ≤ ‖curve source - curve target‖)
    (closed : curve lower = curve upper) :
    contourVelocity curve tangent target lower upper =
      (1 / (4 * Real.pi)) •
        ∫ source in Icc lower upper, contourChordPhase curve target source * star (tangent source) := by
  have ordered : lower ≤ upper := target_mem.1.le.trans target_mem.2.le
  have tangent_integrable : IntervalIntegrable tangent volume lower upper :=
    tangent_continuous.continuousOn.intervalIntegrable_of_Icc ordered
  have phase_integrable : IntervalIntegrable
      (fun source => contourChordPhase curve target source * star (tangent source)) volume lower upper :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr
      (contourChordPhase_integrable curve_continuous tangent_continuous tangent_bound)
  have log_integrable := contour_log_integrable_interval ordered ⟨target_mem.1.le, target_mem.2.le⟩
    speed_pos chord_pos curve_continuous tangent_continuous derivative tangent_bound chord_bound
  have rest_integrable := (tangent_integrable.add phase_integrable).div_const (2 : ℂ)
  have boundary := integral_eq_sub_of_hasDerivAt_except_point (singular := target) ordered
    (continuous_log_norm_smul.comp (curve_continuous.sub continuous_const)).continuousOn
    (derivative := fun source => Real.log ‖curve source - curve target‖ • tangent source +
      (tangent source + contourChordPhase curve target source * star (tangent source)) / 2)
    (by
      intro source source_mem distinct
      have separated : curve source - curve target ≠ 0 :=
        norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
          (chord_bound source ⟨source_mem.1.le, source_mem.2.le⟩)))
      have actual := contour_log_product_source_derivative
        (derivative source ⟨source_mem.1.le, source_mem.2.le⟩) separated
      rw [contourChordPhase_swap curve source target] at actual
      exact actual)
    (log_integrable.add rest_integrable)
  rw [intervalIntegral.integral_add log_integrable rest_integrable,
    intervalIntegral.integral_div,
    intervalIntegral.integral_add tangent_integrable phase_integrable] at boundary
  have tangent_integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun source membership => derivative source (by simpa only [uIcc_of_le ordered] using membership))
    tangent_integrable
  rw [tangent_integral] at boundary
  simp only [Function.comp_apply, closed, sub_self, zero_add] at boundary
  have log_identity :
      (∫ source in lower..upper, Real.log ‖curve source - curve target‖ • tangent source) =
        -((∫ source in lower..upper, contourChordPhase curve target source * star (tangent source)) / 2) :=
    eq_neg_iff_add_eq_zero.mpr boundary
  have phase_interval :
      (∫ source in Icc lower upper, contourChordPhase curve target source * star (tangent source)) =
        ∫ source in lower..upper, contourChordPhase curve target source * star (tangent source) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ordered]
  unfold contourVelocity
  have norm_reverse : (fun source => Real.log ‖curve target - curve source‖ • tangent source) =
      fun source => Real.log ‖curve source - curve target‖ • tangent source := by
    funext source
    rw [norm_sub_rev]
  rw [norm_reverse]
  rw [log_identity, phase_interval, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

theorem hasDerivAt_contourVelocity {curve tangent : ℝ → ℂ}
    {target parameterRadius lower upper holder speed chord : ℝ}
    (parameterRadius_pos : 0 < parameterRadius)
    (holder_nonneg : 0 ≤ holder) (speed_pos : 0 < speed) (chord_pos : 0 < chord)
    (lower_bound : lower ≤ target - parameterRadius) (upper_bound : target + parameterRadius ≤ upper)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_nonzero : ∀ x ∈ Icc lower upper, tangent x ≠ 0)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : ∀ parameter ∈ Icc (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        chord * |parameter - source| ≤ ‖curve parameter - curve source‖)
    (closed : curve lower = curve upper) :
    HasDerivAt (fun parameter => contourVelocity curve tangent parameter lower upper)
      ((1 / (4 * Real.pi)) • ∫ source in Icc lower upper,
        contourChordPhaseDerivative curve tangent target source * star (tangent source)) target := by
  have phase_derivative := hasDerivAt_contourChordPhase_integral parameterRadius_pos holder_nonneg
    speed_pos.le chord_pos lower_bound upper_bound curve_continuous tangent_continuous derivative
    tangent_nonzero tangent_bound holder_bound chord_bound
  apply (HasDerivAt.const_smul (1 / (4 * Real.pi) : ℝ) phase_derivative).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by linarith : target - parameterRadius < target)
    (by linarith : target < target + parameterRadius)] with parameter membership
  apply contourVelocity_eq_phase_integral_general
    (target_mem := ⟨lower_bound.trans_lt membership.1, membership.2.trans_le upper_bound⟩)
    speed_pos chord_pos curve_continuous tangent_continuous derivative tangent_bound
  · intro source source_mem
    simpa only [abs_sub_comm source parameter, norm_sub_rev (curve source) (curve parameter)] using
      chord_bound parameter ⟨membership.1.le, membership.2.le⟩ source source_mem
  · exact closed

theorem contDiffOn_one_contourVelocity {curve tangent : ℝ → ℂ}
    {target parameterRadius lower upper holder speed chord : ℝ}
    (parameterRadius_pos : 0 < parameterRadius)
    (holder_nonneg : 0 ≤ holder) (speed_pos : 0 < speed) (chord_pos : 0 < chord)
    (lower_bound : lower ≤ target - parameterRadius) (upper_bound : target + parameterRadius ≤ upper)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (tangent_nonzero : ∀ x ∈ Icc lower upper, tangent x ≠ 0)
    (tangent_bound : ∀ x ∈ Icc lower upper, ‖tangent x‖ ≤ speed)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : ∀ parameter ∈ Icc (target - parameterRadius) (target + parameterRadius),
      ∀ source ∈ Icc lower upper,
        chord * |parameter - source| ≤ ‖curve parameter - curve source‖)
    (closed : curve lower = curve upper) :
    ContDiffOn ℝ 1 (fun parameter => contourVelocity curve tangent parameter lower upper)
      (Ioo (target - parameterRadius / 2) (target + parameterRadius / 2)) := by
  let domain := Ioo (target - parameterRadius / 2) (target + parameterRadius / 2)
  let velocityDerivative := fun parameter => (1 / (4 * Real.pi)) •
    ∫ source in Icc lower upper, contourChordPhaseDerivative curve tangent parameter source * star (tangent source)
  have local_lower : ∀ current ∈ domain, lower ≤ current - parameterRadius / 2 := by
    intro current membership
    linarith [membership.1]
  have local_upper : ∀ current ∈ domain, current + parameterRadius / 2 ≤ upper := by
    intro current membership
    linarith [membership.2]
  have local_subset : ∀ current ∈ domain,
      Icc (current - parameterRadius / 2) (current + parameterRadius / 2) ⊆
        Icc (target - parameterRadius) (target + parameterRadius) := by
    intro current membership parameter parameter_mem
    constructor <;> linarith [membership.1, membership.2, parameter_mem.1, parameter_mem.2]
  have velocity_derivative : ∀ current ∈ domain,
      HasDerivAt (fun parameter => contourVelocity curve tangent parameter lower upper)
        (velocityDerivative current) current := by
    intro current membership
    exact hasDerivAt_contourVelocity (parameterRadius := parameterRadius / 2) (by positivity)
      holder_nonneg speed_pos chord_pos (local_lower current membership) (local_upper current membership)
      curve_continuous tangent_continuous derivative tangent_nonzero tangent_bound holder_bound
      (fun parameter parameter_mem source source_mem =>
        chord_bound parameter (local_subset current membership parameter_mem) source source_mem) closed
  have derivative_continuous : ContinuousOn velocityDerivative domain := by
    intro current membership
    have actual := contourChordPhaseDerivative_integral_continuousAt
      (target := current) (parameterRadius := parameterRadius / 2) (by positivity)
      holder_nonneg speed_pos.le chord_pos (local_lower current membership) (local_upper current membership)
      derivative tangent_continuous.continuousOn tangent_bound holder_bound
      (fun parameter parameter_mem source source_mem => chord_bound parameter
        (local_subset current membership ⟨parameter_mem.1.le, parameter_mem.2.le⟩) source source_mem)
    exact (continuousAt_const.smul actual).continuousWithinAt
  have actual_derivative_continuous : ContinuousOn
      (deriv (fun parameter => contourVelocity curve tangent parameter lower upper)) domain :=
    derivative_continuous.congr (fun current membership => (velocity_derivative current membership).deriv)
  change ContDiffOn ℝ (0 + 1) (fun parameter => contourVelocity curve tangent parameter lower upper) domain
  rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun current membership => (velocity_derivative current membership).differentiableAt.differentiableWithinAt,
    ?_, contDiffOn_zero.mpr actual_derivative_continuous⟩
  simp

end EulerNonuniqueness.Paper
