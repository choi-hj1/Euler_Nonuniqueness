import EulerNonuniqueness.Section3.WeakSingularIntegral
import EulerNonuniqueness.Section3.RankineContour
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

noncomputable def contourDividedChordRatio (curve reference : ℝ → ℂ) (target source : ℝ) : ℂ :=
  dslope curve target source / dslope reference target source

theorem contourDividedChordRatio_of_ne (curve reference : ℝ → ℂ) {target source : ℝ}
    (distinct : source ≠ target) :
    contourDividedChordRatio curve reference target source =
      (curve source - curve target) / (reference source - reference target) := by
  unfold contourDividedChordRatio
  rw [dslope_of_ne curve distinct, dslope_of_ne reference distinct, slope_def_module, slope_def_module]
  simp only [Complex.real_smul]
  apply mul_div_mul_left
  have scalar_ne : (source - target)⁻¹ ≠ 0 := inv_ne_zero (sub_ne_zero.mpr distinct)
  exact_mod_cast scalar_ne

theorem contour_dslope_difference_bound {curve reference tangent referenceTangent : ℝ → ℂ}
    {lower upper target source difference : ℝ}
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (curve_derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (derivative_difference : ∀ x ∈ Icc lower upper, ‖tangent x - referenceTangent x‖ ≤ difference) :
    ‖dslope curve target source - dslope reference target source‖ ≤ difference := by
  by_cases equal : source = target
  · subst source
    rw [dslope_same, dslope_same, (curve_derivative target target_mem).deriv,
      (reference_derivative target target_mem).deriv]
    exact derivative_difference target target_mem
  have increment := (convex_Icc lower upper).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => ((curve_derivative x hx).sub (reference_derivative x hx)).hasDerivWithinAt)
    derivative_difference target_mem source_mem
  have increment_identity :
      (curve source - reference source) - (curve target - reference target) =
        (curve source - curve target) - (reference source - reference target) := by abel
  rw [increment_identity, Real.norm_eq_abs] at increment
  rw [dslope_of_ne curve equal, dslope_of_ne reference equal, slope_def_module, slope_def_module,
    ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv]
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr equal)
  calc
    _ ≤ |source - target|⁻¹ * (difference * |source - target|) :=
      mul_le_mul_of_nonneg_left increment (by positivity)
    _ = _ := by field_simp

theorem contour_dslope_lower_bound {reference referenceTangent : ℝ → ℂ}
    {lower upper target source chord : ℝ} (source_mem : source ∈ Icc lower upper)
    (reference_derivative : HasDerivAt reference (referenceTangent target) target)
    (tangent_lower : chord ≤ ‖referenceTangent target‖)
    (chord_bound : ∀ x ∈ Icc lower upper,
      chord * |x - target| ≤ ‖reference x - reference target‖) :
    chord ≤ ‖dslope reference target source‖ := by
  by_cases equal : source = target
  · subst source
    rw [dslope_same, reference_derivative.deriv]
    exact tangent_lower
  rw [dslope_of_ne reference equal, slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv]
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr equal)
  calc
    _ = |source - target|⁻¹ * (chord * |source - target|) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left (chord_bound source source_mem) (by positivity)

theorem contourDividedChordRatio_near_one {curve reference tangent referenceTangent : ℝ → ℂ}
    {lower upper target source difference chord : ℝ}
    (difference_nonneg : 0 ≤ difference) (chord_pos : 0 < chord)
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (curve_derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (derivative_difference : ∀ x ∈ Icc lower upper, ‖tangent x - referenceTangent x‖ ≤ difference)
    (tangent_lower : chord ≤ ‖referenceTangent target‖)
    (chord_bound : ∀ x ∈ Icc lower upper,
      chord * |x - target| ≤ ‖reference x - reference target‖) :
    ‖contourDividedChordRatio curve reference target source - 1‖ ≤ difference / chord := by
  have denominator_lower := contour_dslope_lower_bound source_mem (reference_derivative target target_mem)
    tangent_lower chord_bound
  have denominator_ne : dslope reference target source ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (chord_pos.trans_le denominator_lower))
  unfold contourDividedChordRatio
  rw [div_sub_one denominator_ne, norm_div]
  calc
    _ ≤ difference / ‖dslope reference target source‖ := div_le_div_of_nonneg_right
      (contour_dslope_difference_bound target_mem source_mem curve_derivative reference_derivative derivative_difference)
      (norm_nonneg _)
    _ ≤ _ := div_le_div_of_nonneg_left difference_nonneg chord_pos denominator_lower

theorem contourCauchyRemainder_bound_unordered {curve tangent : ℝ → ℂ}
    {target source lower upper holder chord : ℝ}
    (distinct : source ≠ target) (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (chord_bound : chord * |source - target| ≤ ‖curve target - curve source‖) :
    ‖contourCauchyRemainder curve tangent target source‖ ≤
      (holder / chord) / Real.sqrt |source - target| := by
  have distance_pos : 0 < |source - target| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  have ordered := target_mem.1.trans target_mem.2
  have interval_subset : uIcc target source ⊆ Icc lower upper := by
    have subset := uIcc_subset_uIcc_iff_mem.mpr
      ⟨show target ∈ uIcc lower upper by simpa only [uIcc_of_le ordered] using target_mem,
        show source ∈ uIcc lower upper by simpa only [uIcc_of_le ordered] using source_mem⟩
    simpa only [uIcc_of_le ordered] using subset
  have remainder := contour_taylor_remainder_unordered holder_nonneg
    (fun x hx => derivative x (interval_subset hx))
    (fun x hx => holder_bound x (interval_subset hx) source source_mem)
  have numerator : ‖curve target - curve source + (source - target) • tangent source‖ ≤
      holder * Real.sqrt |source - target| * |source - target| := by
    convert remainder using 1
    rw [← norm_neg]
    congr 1
    abel
  have norm_positive := (mul_pos chord_pos distance_pos).trans_le chord_bound
  have curve_ne := norm_ne_zero_iff.mp norm_positive.ne'
  have scalar_ne : ((source - target : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr distinct
  have identity : contourCauchyRemainder curve tangent target source =
      (curve target - curve source + (source - target) • tangent source) /
        ((curve target - curve source) * ((source - target : ℝ) : ℂ)) := by
    unfold contourCauchyRemainder
    rw [Complex.real_smul]
    have cast_ne : (source : ℂ) - (target : ℂ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr distinct
    push_cast
    field_simp [curve_ne, cast_ne]
    ring
  rw [identity, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply (div_le_iff₀ (mul_pos norm_positive distance_pos)).mpr
  calc
    _ ≤ holder * Real.sqrt |source - target| * |source - target| := numerator
    _ = ((holder / chord) / Real.sqrt |source - target|) *
        (chord * |source - target| * |source - target|) := by
      have algebra : ∀ distance : ℝ, 0 < distance →
          holder * Real.sqrt distance * distance =
            ((holder / chord) / Real.sqrt distance) * (chord * distance * distance) := by
        intro distance positive
        field_simp
        calc
          _ = holder * chord * (Real.sqrt distance ^ 2) * distance := by ring
          _ = _ := by rw [Real.sq_sqrt positive.le]; ring
      exact algebra _ distance_pos
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right chord_bound distance_pos.le) (by positivity)

theorem contourCauchyKernel_difference_bound {curve reference tangent referenceTangent : ℝ → ℂ}
    {target source lower upper holder referenceHolder chord referenceChord : ℝ}
    (holder_nonneg : 0 ≤ holder) (referenceHolder_nonneg : 0 ≤ referenceHolder)
    (chord_pos : 0 < chord) (referenceChord_pos : 0 < referenceChord)
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (reference_holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖referenceTangent x - referenceTangent y‖ ≤ referenceHolder * Real.sqrt |x - y|)
    (chord_bound : chord * |source - target| ≤ ‖curve target - curve source‖)
    (reference_chord_bound : referenceChord * |source - target| ≤ ‖reference target - reference source‖) :
    ‖contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source‖ ≤
      (holder / chord + referenceHolder / referenceChord) * inverseSqrtDistance target source := by
  by_cases equal : source = target
  · subst source
    simp [contourCauchyKernel, inverseSqrtDistance]
  have curve_bound := contourCauchyRemainder_bound_unordered equal holder_nonneg chord_pos
    target_mem source_mem derivative holder_bound chord_bound
  have reference_bound := contourCauchyRemainder_bound_unordered equal referenceHolder_nonneg referenceChord_pos
    target_mem source_mem reference_derivative reference_holder_bound reference_chord_bound
  have identity : contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source =
      contourCauchyRemainder curve tangent target source -
        contourCauchyRemainder reference referenceTangent target source := by
    simp only [contourCauchyKernel, contourCauchyRemainder]
    ring
  rw [identity]
  calc
    _ ≤ ‖contourCauchyRemainder curve tangent target source‖ +
        ‖contourCauchyRemainder reference referenceTangent target source‖ := norm_sub_le _ _
    _ ≤ (holder / chord) / Real.sqrt |source - target| +
        (referenceHolder / referenceChord) / Real.sqrt |source - target| := add_le_add curve_bound reference_bound
    _ = _ := by simp only [inverseSqrtDistance]; ring

theorem contour_chord_lower_of_derivative_close {curve reference tangent referenceTangent : ℝ → ℂ}
    {lower upper target source difference chord : ℝ}
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (curve_derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (derivative_difference : ∀ x ∈ Icc lower upper, ‖tangent x - referenceTangent x‖ ≤ difference)
    (reference_chord : chord * |source - target| ≤ ‖reference source - reference target‖) :
    (chord - difference) * |source - target| ≤ ‖curve source - curve target‖ := by
  have slope_difference := contour_dslope_difference_bound target_mem source_mem
    curve_derivative reference_derivative derivative_difference
  have increment_identity : (curve source - curve target) - (reference source - reference target) =
      (source - target) • (dslope curve target source - dslope reference target source) := by
    rw [smul_sub, sub_smul_dslope, sub_smul_dslope]
  have increment_bound : ‖(curve source - curve target) - (reference source - reference target)‖ ≤
      difference * |source - target| := by
    rw [increment_identity, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left slope_difference (abs_nonneg _)).trans_eq (mul_comm _ _)
  have norm_difference := norm_sub_norm_le (reference source - reference target) (curve source - curve target)
  rw [norm_sub_rev (reference source - reference target) (curve source - curve target)] at norm_difference
  nlinarith

theorem contourDividedChordRatio_continuousOn {curve reference tangent referenceTangent : ℝ → ℂ}
    {lower upper target chord : ℝ} (chord_pos : 0 < chord)
    (curve_continuous : Continuous curve) (reference_continuous : Continuous reference)
    (curve_derivative : HasDerivAt curve (tangent target) target)
    (reference_derivative : HasDerivAt reference (referenceTangent target) target)
    (tangent_lower : chord ≤ ‖referenceTangent target‖)
    (reference_chord : ∀ x ∈ Icc lower upper,
      chord * |x - target| ≤ ‖reference x - reference target‖) :
    ContinuousOn (contourDividedChordRatio curve reference target) (Icc lower upper) := by
  intro source source_mem
  have curve_slope : ContinuousAt (dslope curve target) source := by
    by_cases equal : source = target
    · subst source
      exact continuousAt_dslope_same.mpr curve_derivative.differentiableAt
    · exact (continuousAt_dslope_of_ne equal).mpr curve_continuous.continuousAt
  have reference_slope : ContinuousAt (dslope reference target) source := by
    by_cases equal : source = target
    · subst source
      exact continuousAt_dslope_same.mpr reference_derivative.differentiableAt
    · exact (continuousAt_dslope_of_ne equal).mpr reference_continuous.continuousAt
  have denominator_lower := contour_dslope_lower_bound source_mem reference_derivative tangent_lower reference_chord
  exact (curve_slope.div reference_slope
    (norm_ne_zero_iff.mp (ne_of_gt (chord_pos.trans_le denominator_lower)))).continuousWithinAt

theorem contourDividedChordRatio_mem_slitPlane {curve reference tangent referenceTangent : ℝ → ℂ}
    {lower upper target source difference chord : ℝ}
    (difference_nonneg : 0 ≤ difference) (chord_pos : 0 < chord) (close : difference < chord)
    (target_mem : target ∈ Icc lower upper) (source_mem : source ∈ Icc lower upper)
    (curve_derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (derivative_difference : ∀ x ∈ Icc lower upper, ‖tangent x - referenceTangent x‖ ≤ difference)
    (tangent_lower : chord ≤ ‖referenceTangent target‖)
    (reference_chord : ∀ x ∈ Icc lower upper,
      chord * |x - target| ≤ ‖reference x - reference target‖) :
    contourDividedChordRatio curve reference target source ∈ Complex.slitPlane := by
  have bound := contourDividedChordRatio_near_one difference_nonneg chord_pos target_mem source_mem
    curve_derivative reference_derivative derivative_difference tangent_lower reference_chord
  apply Complex.ball_one_subset_slitPlane
  rw [Metric.mem_ball, dist_eq_norm]
  exact bound.trans_lt ((div_lt_one chord_pos).mpr close)

theorem contourCauchyKernel_difference_integrable {curve reference tangent referenceTangent : ℝ → ℂ}
    {target lower upper holder referenceHolder chord referenceChord : ℝ}
    (holder_nonneg : 0 ≤ holder) (referenceHolder_nonneg : 0 ≤ referenceHolder)
    (chord_pos : 0 < chord) (referenceChord_pos : 0 < referenceChord)
    (target_mem : target ∈ Icc lower upper)
    (curve_continuous : Continuous curve) (reference_continuous : Continuous reference)
    (tangent_continuous : Continuous tangent) (referenceTangent_continuous : Continuous referenceTangent)
    (derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (reference_holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖referenceTangent x - referenceTangent y‖ ≤ referenceHolder * Real.sqrt |x - y|)
    (chord_bound : ∀ source ∈ Icc lower upper,
      chord * |source - target| ≤ ‖curve target - curve source‖)
    (reference_chord_bound : ∀ source ∈ Icc lower upper,
      referenceChord * |source - target| ≤ ‖reference target - reference source‖) :
    IntegrableOn (fun source => contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source) (Icc lower upper) volume := by
  have measurable : Measurable (fun source => contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source) :=
    (tangent_continuous.measurable.div (measurable_const.sub curve_continuous.measurable)).sub
      (referenceTangent_continuous.measurable.div (measurable_const.sub reference_continuous.measurable))
  apply weakSingular_integrable (measurable.aestronglyMeasurable.restrict)
    (bound := holder / chord + referenceHolder / referenceChord)
  intro source source_mem
  exact contourCauchyKernel_difference_bound holder_nonneg referenceHolder_nonneg chord_pos referenceChord_pos
    target_mem source_mem derivative reference_derivative holder_bound reference_holder_bound
    (chord_bound source source_mem) (reference_chord_bound source source_mem)

theorem contourDividedChordRatio_clog_derivative {curve reference tangent referenceTangent : ℝ → ℂ}
    {target source : ℝ} (distinct : source ≠ target)
    (curve_derivative : HasDerivAt curve (tangent source) source)
    (reference_derivative : HasDerivAt reference (referenceTangent source) source)
    (curve_separated : curve source - curve target ≠ 0)
    (reference_separated : reference source - reference target ≠ 0)
    (slit : contourDividedChordRatio curve reference target source ∈ Complex.slitPlane) :
    HasDerivAt (fun current => Complex.log (contourDividedChordRatio curve reference target current))
      (-(contourCauchyKernel curve tangent target source -
        contourCauchyKernel reference referenceTangent target source)) source := by
  have actual_slit : (curve source - curve target) / (reference source - reference target) ∈ Complex.slitPlane := by
    rw [← contourDividedChordRatio_of_ne curve reference distinct]
    exact slit
  have log_derivative := (((curve_derivative.sub_const (curve target)).div
    (reference_derivative.sub_const (reference target)) reference_separated).clog_real actual_slit)
  have curve_reverse : curve target - curve source ≠ 0 := by
    rw [← neg_sub (curve source) (curve target)]
    exact neg_ne_zero.mpr curve_separated
  have reference_reverse : reference target - reference source ≠ 0 := by
    rw [← neg_sub (reference source) (reference target)]
    exact neg_ne_zero.mpr reference_separated
  have algebra :
      ((tangent source * (reference source - reference target) -
        (curve source - curve target) * referenceTangent source) / (reference source - reference target) ^ 2) /
        ((curve source - curve target) / (reference source - reference target)) =
      -(contourCauchyKernel curve tangent target source -
        contourCauchyKernel reference referenceTangent target source) := by
    unfold contourCauchyKernel
    field_simp [curve_separated, reference_separated, curve_reverse, reference_reverse]
    ring
  rw [algebra] at log_derivative
  apply log_derivative.congr_of_eventuallyEq
  filter_upwards [isOpen_ne.mem_nhds distinct] with current membership
  rw [contourDividedChordRatio_of_ne curve reference membership]

theorem contourCauchyKernel_difference_integral_zero
    {curve reference tangent referenceTangent : ℝ → ℂ}
    {target lower upper holder referenceHolder difference chord : ℝ}
    (target_mem : target ∈ Ioo lower upper)
    (holder_nonneg : 0 ≤ holder) (referenceHolder_nonneg : 0 ≤ referenceHolder)
    (difference_nonneg : 0 ≤ difference) (chord_pos : 0 < chord) (close : difference < chord)
    (curve_continuous : Continuous curve) (reference_continuous : Continuous reference)
    (tangent_continuous : Continuous tangent) (referenceTangent_continuous : Continuous referenceTangent)
    (curve_derivative : ∀ x ∈ Icc lower upper, HasDerivAt curve (tangent x) x)
    (reference_derivative : ∀ x ∈ Icc lower upper, HasDerivAt reference (referenceTangent x) x)
    (derivative_difference : ∀ x ∈ Icc lower upper, ‖tangent x - referenceTangent x‖ ≤ difference)
    (holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |x - y|)
    (reference_holder_bound : ∀ x ∈ Icc lower upper, ∀ y ∈ Icc lower upper,
      ‖referenceTangent x - referenceTangent y‖ ≤ referenceHolder * Real.sqrt |x - y|)
    (tangent_lower : chord ≤ ‖referenceTangent target‖)
    (reference_chord : ∀ x ∈ Icc lower upper,
      chord * |x - target| ≤ ‖reference x - reference target‖)
    (curve_closed : curve lower = curve upper) (reference_closed : reference lower = reference upper) :
    (∫ source in Icc lower upper, contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source) = 0 := by
  have target_closed : target ∈ Icc lower upper := ⟨target_mem.1.le, target_mem.2.le⟩
  have ordered : lower ≤ upper := target_mem.1.le.trans target_mem.2.le
  have curve_chord : ∀ source ∈ Icc lower upper,
      (chord - difference) * |source - target| ≤ ‖curve source - curve target‖ := by
    intro source source_mem
    exact contour_chord_lower_of_derivative_close target_closed source_mem curve_derivative
      reference_derivative derivative_difference (reference_chord source source_mem)
  have ratio_slit : ∀ source ∈ Icc lower upper,
      contourDividedChordRatio curve reference target source ∈ Complex.slitPlane := by
    intro source source_mem
    exact contourDividedChordRatio_mem_slitPlane difference_nonneg chord_pos close target_closed source_mem
      curve_derivative reference_derivative derivative_difference tangent_lower reference_chord
  have ratio_continuous := contourDividedChordRatio_continuousOn (tangent := tangent)
    (referenceTangent := referenceTangent) chord_pos curve_continuous reference_continuous
    (curve_derivative target target_closed) (reference_derivative target target_closed) tangent_lower reference_chord
  have log_continuous : ContinuousOn (fun source => Complex.log (contourDividedChordRatio curve reference target source))
      (Icc lower upper) := by
    intro source source_mem
    exact (continuousAt_clog (ratio_slit source source_mem)).comp_continuousWithinAt
      (ratio_continuous source source_mem)
  have difference_integrable := contourCauchyKernel_difference_integrable holder_nonneg referenceHolder_nonneg
    (by linarith : 0 < chord - difference) chord_pos target_closed curve_continuous reference_continuous
    tangent_continuous referenceTangent_continuous curve_derivative reference_derivative holder_bound
    reference_holder_bound
    (fun source source_mem => by simpa only [norm_sub_rev] using curve_chord source source_mem)
    (fun source source_mem => by simpa only [norm_sub_rev] using reference_chord source source_mem)
  have interval_integrable := (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr difference_integrable
  have boundary := integral_eq_sub_of_hasDerivAt_except_point (singular := target) ordered log_continuous
    (derivative := fun source => -(contourCauchyKernel curve tangent target source -
      contourCauchyKernel reference referenceTangent target source))
    (by
      intro source source_mem distinct
      have curve_separated : curve source - curve target ≠ 0 :=
        norm_ne_zero_iff.mp (ne_of_gt ((mul_pos (by linarith : 0 < chord - difference)
          (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
            (curve_chord source ⟨source_mem.1.le, source_mem.2.le⟩)))
      have reference_separated : reference source - reference target ≠ 0 :=
        norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos (abs_pos.mpr (sub_ne_zero.mpr distinct))).trans_le
          (reference_chord source ⟨source_mem.1.le, source_mem.2.le⟩)))
      exact contourDividedChordRatio_clog_derivative distinct
        (curve_derivative source ⟨source_mem.1.le, source_mem.2.le⟩)
        (reference_derivative source ⟨source_mem.1.le, source_mem.2.le⟩)
        curve_separated reference_separated (ratio_slit source ⟨source_mem.1.le, source_mem.2.le⟩))
    interval_integrable.neg
  have endpoints : contourDividedChordRatio curve reference target upper =
      contourDividedChordRatio curve reference target lower := by
    rw [contourDividedChordRatio_of_ne curve reference target_mem.2.ne',
      contourDividedChordRatio_of_ne curve reference target_mem.1.ne,
      curve_closed, reference_closed]
  rw [endpoints, sub_self, intervalIntegral.integral_neg] at boundary
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ordered]
  exact neg_eq_zero.mp boundary

theorem principal_value_tendsto_symmetric_integral {kernel : ℝ → ℂ} {radius : ℝ}
    (radius_pos : 0 < radius)
    (kernel_continuous : ContinuousOn kernel (Icc (-radius) radius \ {0}))
    (symmetric_integrable : IntegrableOn (fun source => kernel source + kernel (-source)) (Ioo 0 radius)) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), kernel source) + ∫ source in cutoff..radius, kernel source)
      (𝓝[>] 0) (𝓝 (∫ source in (0 : ℝ)..radius, kernel source + kernel (-source))) := by
  have closed_integrable : IntegrableOn (fun source => kernel source + kernel (-source)) (uIcc 0 radius) := by
    rw [uIcc_of_le radius_pos.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact symmetric_integrable
  have continuous := intervalIntegral.continuousOn_primitive_interval_left closed_integrable
  have limit := continuous 0 (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 radius)
  rw [ContinuousWithinAt, uIcc_of_le radius_pos.le, nhdsWithin_Icc_eq_nhdsGE radius_pos] at limit
  apply (limit.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)).congr'
  filter_upwards [Ioo_mem_nhdsGT radius_pos] with cutoff cutoff_mem
  have positive_continuous : ContinuousOn kernel (Icc cutoff radius) := by
    apply kernel_continuous.mono
    intro source source_mem
    exact ⟨⟨by linarith [source_mem.1, cutoff_mem.1], source_mem.2⟩,
      by simp only [mem_singleton_iff]; linarith [source_mem.1, cutoff_mem.1]⟩
  have negative_continuous : ContinuousOn (fun source => kernel (-source)) (Icc cutoff radius) := by
    apply kernel_continuous.comp continuousOn_neg
    intro source source_mem
    refine ⟨⟨by linarith [source_mem.2], by linarith [source_mem.1, cutoff_mem.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [source_mem.1, cutoff_mem.1]
  rw [intervalIntegral.integral_add
    (positive_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le)
    (negative_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le),
    intervalIntegral.integral_comp_neg kernel]
  exact add_comm _ _

theorem unit_circle_cauchy_symmetric {position : ℂ} (nonzero : position ≠ 0) (separated : position ≠ 1) :
    Complex.I * position / (1 - position) + Complex.I * position⁻¹ / (1 - position⁻¹) = -Complex.I := by
  have first_ne : 1 - position ≠ 0 := sub_ne_zero.mpr separated.symm
  have second_ne : 1 - position⁻¹ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro equal
    have inverse_one : position⁻¹ = 1 := equal.symm
    exact separated (inv_eq_one.mp inverse_one)
  have expanded_ne : -1 + position ≠ 0 := by
    rw [add_comm, ← sub_eq_add_neg]
    exact sub_ne_zero.mpr separated
  field_simp [nonzero, first_ne, second_ne, expanded_ne, sub_ne_zero.mpr separated]
  ring

theorem standardCircle_cauchy_symmetric (source : ℝ)
    (source_mem : source ∈ Icc (-Real.pi) Real.pi) (distinct : source ≠ 0) :
    contourCauchyKernel standardCircle standardCircleTangent 0 source +
      contourCauchyKernel standardCircle standardCircleTangent 0 (-source) = -Complex.I := by
  have nonzero : standardCircle source ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
  have separated : standardCircle source ≠ 1 := by
    have chord := standardCircle_chord_bound source source_mem
    have positive : 0 < (2 / Real.pi) * |source| := by positivity
    intro equal
    have zero_circle : standardCircle 0 = 1 := by simp [standardCircle]
    rw [equal, zero_circle, sub_self, norm_zero] at chord
    exact (not_le_of_gt positive) chord
  have reflected : standardCircle (-source) = (standardCircle source)⁻¹ := by
    simp [standardCircle, Complex.exp_neg]
  simpa only [contourCauchyKernel, standardCircleTangent, reflected,
    show standardCircle 0 = 1 by simp [standardCircle]] using unit_circle_cauchy_symmetric nonzero separated

theorem standardCircle_cauchy_principal_value :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (-Real.pi)..(-cutoff), contourCauchyKernel standardCircle standardCircleTangent 0 source) +
        ∫ source in cutoff..Real.pi, contourCauchyKernel standardCircle standardCircleTangent 0 source)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have curve_continuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr (fun parameter => (standardCircle_derivative parameter).continuousAt)
  have tangent_continuous : Continuous standardCircleTangent := by
    change Continuous (fun parameter => Complex.I * standardCircle parameter)
    exact continuous_const.mul curve_continuous
  have kernel_continuous : ContinuousOn (contourCauchyKernel standardCircle standardCircleTangent 0)
      (Icc (-Real.pi) Real.pi \ {0}) := by
    apply tangent_continuous.continuousOn.div (continuousOn_const.sub curve_continuous.continuousOn)
    intro source source_mem
    have distinct : source ≠ 0 := by simpa using source_mem.2
    have chord := standardCircle_chord_bound source source_mem.1
    have positive : 0 < (2 / Real.pi) * |source| := by positivity
    apply norm_ne_zero_iff.mp
    rw [norm_sub_rev]
    exact ne_of_gt (positive.trans_le chord)
  have finite : volume (Ioo (0 : ℝ) Real.pi) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have symmetric_integrable : IntegrableOn (fun source =>
      contourCauchyKernel standardCircle standardCircleTangent 0 source +
        contourCauchyKernel standardCircle standardCircleTangent 0 (-source)) (Ioo 0 Real.pi) volume := by
    apply (integrableOn_const.2 (Or.inr finite) :
      IntegrableOn (fun _ : ℝ => -Complex.I) (Ioo 0 Real.pi) volume).congr_fun _ measurableSet_Ioo
    intro source source_mem
    exact (standardCircle_cauchy_symmetric source
      ⟨by linarith [Real.pi_pos, source_mem.1], source_mem.2.le⟩ source_mem.1.ne').symm
  have integral_value : (∫ source in (0 : ℝ)..Real.pi,
      contourCauchyKernel standardCircle standardCircleTangent 0 source +
        contourCauchyKernel standardCircle standardCircleTangent 0 (-source)) = -(Real.pi : ℂ) * Complex.I := by
    have integral_eq : (∫ source in (0 : ℝ)..Real.pi,
        contourCauchyKernel standardCircle standardCircleTangent 0 source +
          contourCauchyKernel standardCircle standardCircleTangent 0 (-source)) =
        ∫ _ in (0 : ℝ)..Real.pi, -Complex.I := by
      apply intervalIntegral.integral_congr_ae
      have nonzero : ∀ᵐ source : ℝ ∂volume, source ≠ 0 := by
        simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
      filter_upwards [nonzero] with source distinct source_mem
      rw [uIoc_of_le Real.pi_pos.le] at source_mem
      exact standardCircle_cauchy_symmetric source
        ⟨by linarith [Real.pi_pos, source_mem.1], source_mem.2⟩ distinct
    rw [integral_eq, intervalIntegral.integral_const]
    simp [Complex.real_smul]
  have limit := principal_value_tendsto_symmetric_integral Real.pi_pos kernel_continuous symmetric_integrable
  rw [integral_value] at limit
  exact limit

theorem truncatedIntegral_tendsto_integral {kernel : ℝ → ℂ} {radius : ℝ}
    (radius_pos : 0 < radius) (integrable : IntervalIntegrable kernel volume (-radius) radius) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), kernel source) + ∫ source in cutoff..radius, kernel source)
      (𝓝[>] 0) (𝓝 (∫ source in (-radius)..radius, kernel source)) := by
  have ordered : -radius ≤ radius := by linarith
  have closed_integrable : IntegrableOn kernel (uIcc (-radius) radius) volume := by
    rw [uIcc_of_le ordered]
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mp integrable
  have left_continuous : ContinuousOn (fun cutoff => ∫ source in (-radius)..cutoff, kernel source)
      (Icc (-radius) radius) := by
    simpa only [uIcc_of_le ordered] using intervalIntegral.continuousOn_primitive_interval closed_integrable
  have right_continuous : ContinuousOn (fun cutoff => ∫ source in cutoff..radius, kernel source)
      (Icc (-radius) radius) := by
    simpa only [uIcc_of_le ordered] using intervalIntegral.continuousOn_primitive_interval_left closed_integrable
  have zero_mem : (0 : ℝ) ∈ Icc (-radius) radius := ⟨by linarith, radius_pos.le⟩
  have neighborhood : Icc (-radius) radius ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by linarith) radius_pos
  have left_at : ContinuousAt (fun cutoff : ℝ => ∫ source in (-radius)..cutoff, kernel source) 0 :=
    (left_continuous 0 zero_mem).continuousAt neighborhood
  have right_at : ContinuousAt (fun cutoff : ℝ => ∫ source in cutoff..radius, kernel source) 0 :=
    (right_continuous 0 zero_mem).continuousAt neighborhood
  have total_at : ContinuousAt (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), kernel source) + ∫ source in cutoff..radius, kernel source) 0 := by
    have reflected_left : ContinuousAt (fun cutoff : ℝ => ∫ source in (-radius)..(-cutoff), kernel source) 0 :=
      left_at.comp_of_eq (continuousAt_id.neg) (by simp)
    exact reflected_left.add right_at
  have zero_u_mem : (0 : ℝ) ∈ uIcc (-radius) radius := by
    simpa only [uIcc_of_le ordered] using zero_mem
  have value := intervalIntegral.integral_add_adjacent_intervals
    (integrable.mono_set (uIcc_subset_uIcc_left zero_u_mem))
    (integrable.mono_set (uIcc_subset_uIcc_right zero_u_mem))
  simpa only [neg_zero, value] using total_at.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

theorem principal_value_sub_eq_integral_difference {first second : ℝ → ℂ}
    {radius : ℝ} {firstValue secondValue : ℂ} (radius_pos : 0 < radius)
    (first_continuous : ContinuousOn first (Icc (-radius) radius \ {0}))
    (second_continuous : ContinuousOn second (Icc (-radius) radius \ {0}))
    (difference_integrable : IntervalIntegrable (fun source => first source - second source) volume (-radius) radius)
    (first_limit : Tendsto (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), first source) + ∫ source in cutoff..radius, first source)
      (𝓝[>] 0) (𝓝 firstValue))
    (second_limit : Tendsto (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), second source) + ∫ source in cutoff..radius, second source)
      (𝓝[>] 0) (𝓝 secondValue)) :
    firstValue - secondValue = ∫ source in (-radius)..radius, first source - second source := by
  have difference_limit : Tendsto (fun cutoff : ℝ =>
      (∫ source in (-radius)..(-cutoff), first source - second source) +
        ∫ source in cutoff..radius, first source - second source)
      (𝓝[>] 0) (𝓝 (firstValue - secondValue)) := by
    apply (first_limit.sub second_limit).congr'
    filter_upwards [Ioo_mem_nhdsGT radius_pos] with cutoff cutoff_mem
    have left_subset : Icc (-radius) (-cutoff) ⊆ Icc (-radius) radius \ {0} := by
      intro source membership
      refine ⟨⟨membership.1, by linarith [membership.2, cutoff_mem.1]⟩, ?_⟩
      simp only [mem_singleton_iff]
      linarith [membership.2, cutoff_mem.1]
    have right_subset : Icc cutoff radius ⊆ Icc (-radius) radius \ {0} := by
      intro source membership
      refine ⟨⟨by linarith [membership.1, cutoff_mem.1], membership.2⟩, ?_⟩
      simp only [mem_singleton_iff]
      linarith [membership.1, cutoff_mem.1]
    rw [intervalIntegral.integral_sub
      ((first_continuous.mono left_subset).intervalIntegrable_of_Icc (by linarith [cutoff_mem.2]))
      ((second_continuous.mono left_subset).intervalIntegrable_of_Icc (by linarith [cutoff_mem.2])),
      intervalIntegral.integral_sub
      ((first_continuous.mono right_subset).intervalIntegrable_of_Icc cutoff_mem.2.le)
      ((second_continuous.mono right_subset).intervalIntegrable_of_Icc cutoff_mem.2.le)]
    ring
  exact tendsto_nhds_unique difference_limit (truncatedIntegral_tendsto_integral radius_pos difference_integrable)

theorem standardCircleTangent_derivative (source : ℝ) :
    HasDerivAt standardCircleTangent (Complex.I * standardCircleTangent source) source := by
  change HasDerivAt (fun current => Complex.I * standardCircle current)
    (Complex.I * standardCircleTangent source) source
  exact (standardCircle_derivative source).const_mul Complex.I

theorem standardCircleTangent_holder_half (first second : ℝ)
    (first_mem : first ∈ Icc (-Real.pi) Real.pi) (second_mem : second ∈ Icc (-Real.pi) Real.pi) :
    ‖standardCircleTangent first - standardCircleTangent second‖ ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt |first - second| := by
  have bound := contour_speed_bound_on_interval
    (fun source _ => standardCircleTangent_derivative source)
    (speed := 1) (fun source _ => by simp [norm_mul, standardCircleTangent_norm]) second_mem first_mem
  have distance : |first - second| ≤ 2 * Real.pi := by
    apply abs_le.mpr
    constructor <;> linarith [first_mem.1, first_mem.2, second_mem.1, second_mem.2]
  calc
    _ ≤ |first - second| := by simpa only [one_mul] using bound
    _ = Real.sqrt |first - second| * Real.sqrt |first - second| := (Real.mul_self_sqrt (abs_nonneg _)).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt distance) (Real.sqrt_nonneg _)

theorem contourCauchy_near_circle_principal_value {curve tangent : ℝ → ℂ}
    {holder difference : ℝ} (holder_nonneg : 0 ≤ holder) (difference_nonneg : 0 ≤ difference)
    (close : difference < 2 / Real.pi)
    (curve_continuous : Continuous curve) (tangent_continuous : Continuous tangent)
    (derivative : ∀ source ∈ Icc (-Real.pi) Real.pi, HasDerivAt curve (tangent source) source)
    (holder_bound : ∀ first ∈ Icc (-Real.pi) Real.pi, ∀ second ∈ Icc (-Real.pi) Real.pi,
      ‖tangent first - tangent second‖ ≤ holder * Real.sqrt |first - second|)
    (derivative_difference : ∀ source ∈ Icc (-Real.pi) Real.pi,
      ‖tangent source - standardCircleTangent source‖ ≤ difference)
    (closed : curve (-Real.pi) = curve Real.pi) :
    Tendsto (fun cutoff : ℝ =>
      (∫ source in (-Real.pi)..(-cutoff), contourCauchyKernel curve tangent 0 source) +
        ∫ source in cutoff..Real.pi, contourCauchyKernel curve tangent 0 source)
      (𝓝[>] 0) (𝓝 (-(Real.pi : ℂ) * Complex.I)) := by
  have zero_mem : (0 : ℝ) ∈ Ioo (-Real.pi) Real.pi := ⟨by linarith [Real.pi_pos], Real.pi_pos⟩
  have zero_closed : (0 : ℝ) ∈ Icc (-Real.pi) Real.pi := ⟨zero_mem.1.le, zero_mem.2.le⟩
  have chord_pos : 0 < 2 / Real.pi := by positivity
  have perturbed_chord_pos : 0 < 2 / Real.pi - difference := by linarith
  have circle_continuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr (fun source => (standardCircle_derivative source).continuousAt)
  have circle_tangent_continuous : Continuous standardCircleTangent := by
    change Continuous (fun source => Complex.I * standardCircle source)
    exact continuous_const.mul circle_continuous
  have circle_closed : standardCircle (-Real.pi) = standardCircle Real.pi := by
    simp [standardCircle, Complex.exp_neg, Complex.exp_pi_mul_I]
  have circle_chord : ∀ source ∈ Icc (-Real.pi) Real.pi,
      (2 / Real.pi) * |source - 0| ≤ ‖standardCircle source - standardCircle 0‖ := by
    intro source source_mem
    simpa only [sub_zero] using standardCircle_chord_bound source source_mem
  have tangent_lower : 2 / Real.pi ≤ ‖standardCircleTangent 0‖ := by
    rw [standardCircleTangent_norm]
    exact (div_le_one Real.pi_pos).mpr Real.two_le_pi
  have curve_chord : ∀ source ∈ Icc (-Real.pi) Real.pi,
      (2 / Real.pi - difference) * |source| ≤ ‖curve source - curve 0‖ := by
    intro source source_mem
    simpa only [sub_zero] using contour_chord_lower_of_derivative_close zero_closed source_mem derivative
      (fun source _ => standardCircle_derivative source) derivative_difference (circle_chord source source_mem)
  have zero_integral := contourCauchyKernel_difference_integral_zero zero_mem holder_nonneg
    (Real.sqrt_nonneg (2 * Real.pi)) difference_nonneg chord_pos close curve_continuous circle_continuous
    tangent_continuous circle_tangent_continuous derivative (fun source _ => standardCircle_derivative source)
    derivative_difference holder_bound
    (fun first first_mem second second_mem => standardCircleTangent_holder_half first second first_mem second_mem)
    tangent_lower circle_chord closed circle_closed
  have difference_integrable := contourCauchyKernel_difference_integrable holder_nonneg
    (Real.sqrt_nonneg (2 * Real.pi)) perturbed_chord_pos chord_pos zero_closed curve_continuous circle_continuous
    tangent_continuous circle_tangent_continuous derivative (fun source _ => standardCircle_derivative source)
    holder_bound (fun first first_mem second second_mem =>
      standardCircleTangent_holder_half first second first_mem second_mem)
    (fun source source_mem => by simpa only [sub_zero, norm_sub_rev] using curve_chord source source_mem)
    (fun source source_mem => by simpa only [norm_sub_rev] using circle_chord source source_mem)
  have curve_kernel_continuous : ContinuousOn (contourCauchyKernel curve tangent 0)
      (Icc (-Real.pi) Real.pi \ {0}) := by
    apply tangent_continuous.continuousOn.div (continuousOn_const.sub curve_continuous.continuousOn)
    intro source source_mem
    have distinct : source ≠ 0 := by simpa using source_mem.2
    apply norm_ne_zero_iff.mp
    rw [norm_sub_rev]
    exact ne_of_gt ((mul_pos perturbed_chord_pos (abs_pos.mpr distinct)).trans_le (curve_chord source source_mem.1))
  have circle_kernel_continuous : ContinuousOn (contourCauchyKernel standardCircle standardCircleTangent 0)
      (Icc (-Real.pi) Real.pi \ {0}) := by
    apply circle_tangent_continuous.continuousOn.div (continuousOn_const.sub circle_continuous.continuousOn)
    intro source source_mem
    have distinct : source ≠ 0 := by simpa using source_mem.2
    apply norm_ne_zero_iff.mp
    rw [norm_sub_rev]
    exact ne_of_gt ((mul_pos chord_pos (abs_pos.mpr distinct)).trans_le
      (by simpa only [sub_zero] using circle_chord source source_mem.1))
  obtain ⟨value, limit⟩ := contourCauchy_principal_value_exists Real.pi_pos holder_nonneg perturbed_chord_pos
    derivative tangent_continuous.continuousOn
    (fun first first_mem second second_mem => by
      simpa only [abs_sub_comm first second] using holder_bound first first_mem second second_mem)
    curve_chord
  have ordered : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have comparison := principal_value_sub_eq_integral_difference Real.pi_pos curve_kernel_continuous
    circle_kernel_continuous ((intervalIntegrable_iff_integrableOn_Icc_of_le ordered).mpr difference_integrable)
    limit standardCircle_cauchy_principal_value
  have interval_zero : (∫ source in (-Real.pi)..Real.pi, contourCauchyKernel curve tangent 0 source -
      contourCauchyKernel standardCircle standardCircleTangent 0 source) = 0 := by
    rw [intervalIntegral.integral_of_le ordered, ← integral_Icc_eq_integral_Ioc]
    exact zero_integral
  rw [interval_zero] at comparison
  have value_eq := sub_eq_zero.mp comparison
  rw [value_eq] at limit
  exact limit

end EulerNonuniqueness.Paper
