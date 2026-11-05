import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory Set Filter
open scoped Topology

namespace EulerNonuniqueness.Paper

theorem integral_inv_sqrt_Ioo {radius : ℝ} (radius_pos : 0 < radius) :
    (∫ x in Ioo 0 radius, (Real.sqrt x)⁻¹) = 2 * Real.sqrt radius := by
  have integrand : ∀ x ∈ Ioo 0 radius,
      (Real.sqrt x)⁻¹ = x ^ (-(1 / 2 : ℝ)) := by
    intro x hx
    rw [Real.rpow_neg hx.1.le, Real.sqrt_eq_rpow]
  rw [setIntegral_congr_fun measurableSet_Ioo integrand,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le radius_pos.le,
    integral_rpow (Or.inl (by norm_num))]
  norm_num
  rw [← Real.sqrt_eq_rpow]
  ring

theorem integral_norm_le_inv_sqrt {integrand : ℝ → ℂ} {radius bound : ℝ}
    (radius_pos : 0 < radius)
    (majorized : ∀ x ∈ Ioo 0 radius, ‖integrand x‖ ≤ bound / Real.sqrt x) :
    ‖∫ x in Ioo 0 radius, integrand x‖ ≤ 2 * bound * Real.sqrt radius := by
  have majorant_integrable : IntegrableOn (fun x : ℝ => (Real.sqrt x)⁻¹)
      (Ioo 0 radius) := by
    apply ((intervalIntegral.integrableOn_Ioo_rpow_iff radius_pos).2
      (by norm_num : -1 < -(1 / 2 : ℝ))).congr_fun _ measurableSet_Ioo
    intro x hx
    dsimp
    rw [Real.rpow_neg hx.1.le, Real.sqrt_eq_rpow]
  have estimate := norm_integral_le_of_norm_le (majorant_integrable.const_mul bound)
    (show ∀ᵐ x ∂volume.restrict (Ioo 0 radius),
      ‖integrand x‖ ≤ bound * (Real.sqrt x)⁻¹ from by
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        simpa [div_eq_mul_inv] using majorized x hx)
  rw [integral_const_mul, integral_inv_sqrt_Ioo radius_pos] at estimate
  convert estimate using 1; ring

theorem contour_taylor_remainder_half {curve tangent : ℝ → ℂ} {a b holder : ℝ}
    (ordered : a ≤ b) (holder_nonneg : 0 ≤ holder)
    (differentiable : ∀ x ∈ Icc a b, HasDerivAt curve (tangent x) x)
    (holder_bound : ∀ x ∈ Icc a b,
      ‖tangent x - tangent b‖ ≤ holder * Real.sqrt (b - x)) :
    ‖curve b - curve a - (b - a) • tangent b‖ ≤
      holder * Real.sqrt (b - a) * (b - a) := by
  let remainder : ℝ → ℂ := fun x => curve x - x • tangent b
  have derivative : ∀ x ∈ Icc a b,
      HasDerivWithinAt remainder (tangent x - tangent b) (Icc a b) x := by
    intro x hx
    simpa [remainder] using
      ((differentiable x hx).sub ((hasDerivAt_id x).smul_const (tangent b))).hasDerivWithinAt
  have bound : ∀ x ∈ Ico a b,
      ‖tangent x - tangent b‖ ≤ holder * Real.sqrt (b - a) := by
    intro x hx
    exact (holder_bound x ⟨hx.1, hx.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (sub_le_sub_left hx.1 b)) holder_nonneg)
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment' derivative bound b
    (right_mem_Icc.mpr ordered)
  convert estimate using 1; congr 1; simp [remainder, sub_smul]; abel

noncomputable def contourCauchyRemainder (curve tangent : ℝ → ℂ) (a b : ℝ) : ℂ :=
  tangent b / (curve a - curve b) + ((b - a : ℝ) : ℂ)⁻¹

theorem contourCauchyRemainder_bound {curve tangent : ℝ → ℂ} {a b holder chord : ℝ}
    (ordered : a < b) (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (differentiable : ∀ x ∈ Icc a b, HasDerivAt curve (tangent x) x)
    (holder_bound : ∀ x ∈ Icc a b,
      ‖tangent x - tangent b‖ ≤ holder * Real.sqrt (b - x))
    (chord_bound : chord * (b - a) ≤ ‖curve b - curve a‖) :
    ‖contourCauchyRemainder curve tangent a b‖ ≤
      (holder / chord) / Real.sqrt (b - a) := by
  have length_pos : 0 < b - a := sub_pos.mpr ordered
  have sqrt_pos : 0 < Real.sqrt (b - a) := Real.sqrt_pos.mpr length_pos
  have curve_ne : curve a - curve b ≠ 0 := by
    apply sub_ne_zero.mpr
    intro equal
    have : curve b - curve a = 0 := by rw [equal]; simp
    rw [this, norm_zero] at chord_bound
    nlinarith
  have length_ne : ((b - a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast length_pos.ne'
  have identity : contourCauchyRemainder curve tangent a b =
      (curve a - curve b + (b - a) • tangent b) /
        ((curve a - curve b) * ((b - a : ℝ) : ℂ)) := by
    unfold contourCauchyRemainder
    rw [Complex.real_smul]
    have cast_ne : (b : ℂ) - (a : ℂ) ≠ 0 := by
      exact_mod_cast length_pos.ne'
    push_cast
    field_simp [curve_ne, cast_ne]
    ring
  have numerator : ‖curve a - curve b + (b - a) • tangent b‖ ≤
      holder * Real.sqrt (b - a) * (b - a) := by
    convert contour_taylor_remainder_half ordered.le holder_nonneg differentiable holder_bound
      using 1
    rw [← norm_neg]
    congr 1
    abel
  rw [identity, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos length_pos, norm_sub_rev]
  apply (div_le_iff₀ (mul_pos (lt_of_lt_of_le (mul_pos chord_pos length_pos)
    chord_bound) length_pos)).mpr
  calc
    _ ≤ holder * Real.sqrt (b - a) * (b - a) := numerator
    _ = ((holder / chord) / Real.sqrt (b - a)) *
        (chord * (b - a) * (b - a)) := by
      field_simp
      calc
        _ = holder * chord * (Real.sqrt (b - a) ^ 2) * (b - a) := by ring
        _ = _ := by rw [Real.sq_sqrt length_pos.le]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right chord_bound length_pos.le) (by positivity)

theorem contourCauchyRemainder_integrable {curve tangent : ℝ → ℂ}
    {radius holder chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (differentiable : ∀ x ∈ Icc 0 radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (holder_bound : ∀ x ∈ Icc 0 radius, ∀ y ∈ Icc 0 radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve x - curve 0‖) :
    IntegrableOn (contourCauchyRemainder curve tangent 0) (Ioo 0 radius) := by
  have curve_continuous : ContinuousOn curve (Ioo 0 radius) := by
    intro x hx
    exact (differentiable x ⟨hx.1.le, hx.2.le⟩).continuousAt.continuousWithinAt
  have curve_nonzero : ∀ x ∈ Ioo 0 radius, curve 0 - curve x ≠ 0 := by
    intro x hx equal
    have zero_norm : ‖curve x - curve 0‖ = 0 := by
      rw [sub_eq_zero.mp equal, sub_self, norm_zero]
    have bound := chord_bound x ⟨hx.1, hx.2.le⟩
    rw [zero_norm] at bound
    nlinarith [mul_pos chord_pos hx.1]
  have remainder_continuous : ContinuousOn (contourCauchyRemainder curve tangent 0)
      (Ioo 0 radius) := by
    have first := (tangent_continuous.mono Ioo_subset_Icc_self).div
      (continuousOn_const.sub curve_continuous) curve_nonzero
    have second : ContinuousOn (fun x : ℝ => ((x : ℂ))⁻¹) (Ioo 0 radius) := by
      apply Complex.continuous_ofReal.continuousOn.inv₀
      intro x hx
      exact_mod_cast hx.1.ne'
    change ContinuousOn (fun x => tangent x / (curve 0 - curve x) +
      ((x - 0 : ℝ) : ℂ)⁻¹) (Ioo 0 radius)
    simpa using first.add second
  have majorant : IntegrableOn (fun x : ℝ => (holder / chord) * x ^ (-(1 / 2 : ℝ)))
      (Ioo 0 radius) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff radius_pos).2 (by norm_num)).const_mul _
  apply majorant.mono' (remainder_continuous.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have bound := contourCauchyRemainder_bound hx.1 holder_nonneg chord_pos
    (fun y hy => differentiable y ⟨hy.1, hy.2.trans hx.2.le⟩)
    (fun y hy => by
      simpa [abs_of_nonneg (sub_nonneg.mpr hy.2)] using
        holder_bound y ⟨hy.1, hy.2.trans hx.2.le⟩ x ⟨hx.1.le, hx.2.le⟩)
    (by simpa using chord_bound x ⟨hx.1, hx.2.le⟩)
  rw [Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow]
  simpa only [sub_zero, div_eq_mul_inv] using bound

theorem contourCauchy_symmetric_integrable {curve tangent : ℝ → ℂ}
    {radius holder chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (differentiable : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ x ∈ Icc (-radius) radius, ∀ y ∈ Icc (-radius) radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (chord_bound : ∀ x ∈ Icc (-radius) radius,
      chord * |x| ≤ ‖curve x - curve 0‖) :
    IntegrableOn (fun x => tangent x / (curve 0 - curve x) +
      tangent (-x) / (curve 0 - curve (-x))) (Ioo 0 radius) := by
  have right_mem : ∀ x ∈ Icc 0 radius, x ∈ Icc (-radius) radius := by
    intro x hx
    exact ⟨(neg_nonpos.mpr radius_pos.le).trans hx.1, hx.2⟩
  have left_mem : ∀ x ∈ Icc 0 radius, -x ∈ Icc (-radius) radius := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have right_integrable := contourCauchyRemainder_integrable radius_pos holder_nonneg chord_pos
    (fun x hx => differentiable x (right_mem x hx))
    (tangent_continuous.mono (by intro x hx; exact right_mem x hx))
    (fun x hx y hy => holder_bound x (right_mem x hx) y (right_mem y hy))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))
  have left_integrable := contourCauchyRemainder_integrable (curve := fun x => curve (-x))
    (tangent := fun x => -tangent (-x)) radius_pos holder_nonneg chord_pos
    (fun x hx => by
      convert (differentiable (-x) (left_mem x hx)).scomp x (hasDerivAt_id x).neg using 1
      simp)
    ((tangent_continuous.comp continuousOn_neg (fun x hx => left_mem x hx)).neg)
    (fun x hx y hy => by
      simpa only [neg_sub_neg, norm_sub_rev, neg_sub_neg, abs_sub_comm] using
        holder_bound (-x) (left_mem x hx) (-y) (left_mem y hy))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
  have combined : IntegrableOn (fun x : ℝ => contourCauchyRemainder curve tangent 0 x -
      contourCauchyRemainder (fun y => curve (-y)) (fun y => -tangent (-y)) 0 x)
      (Ioo 0 radius) := right_integrable.sub left_integrable
  apply combined.congr_fun _ measurableSet_Ioo
  intro x hx
  simp only [contourCauchyRemainder, neg_zero, neg_div]
  ring

theorem contourCauchy_symmetric_limit_exists {curve tangent : ℝ → ℂ}
    {radius holder chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (differentiable : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ x ∈ Icc (-radius) radius, ∀ y ∈ Icc (-radius) radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (chord_bound : ∀ x ∈ Icc (-radius) radius,
      chord * |x| ≤ ‖curve x - curve 0‖) :
    ∃ value : ℂ, Tendsto (fun cutoff : ℝ => ∫ x in cutoff..radius,
      (tangent x / (curve 0 - curve x) + tangent (-x) / (curve 0 - curve (-x))))
      (𝓝[>] 0) (𝓝 value) := by
  have integrable := contourCauchy_symmetric_integrable radius_pos holder_nonneg chord_pos
    differentiable tangent_continuous holder_bound chord_bound
  have integrable_closed : IntegrableOn (fun x => tangent x / (curve 0 - curve x) +
      tangent (-x) / (curve 0 - curve (-x))) (uIcc 0 radius) := by
    rw [uIcc_of_le radius_pos.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact integrable
  have continuous := intervalIntegral.continuousOn_primitive_interval_left integrable_closed
  have limit := continuous 0 (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 radius)
  rw [ContinuousWithinAt, uIcc_of_le radius_pos.le,
    nhdsWithin_Icc_eq_nhdsGE radius_pos] at limit
  exact ⟨_, limit.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)⟩

theorem contourCauchy_principal_value_exists {curve tangent : ℝ → ℂ}
    {radius holder chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (differentiable : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ x ∈ Icc (-radius) radius, ∀ y ∈ Icc (-radius) radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (chord_bound : ∀ x ∈ Icc (-radius) radius,
      chord * |x| ≤ ‖curve x - curve 0‖) :
    ∃ value : ℂ, Tendsto (fun cutoff : ℝ =>
      (∫ x in (-radius)..(-cutoff), tangent x / (curve 0 - curve x)) +
        ∫ x in cutoff..radius, tangent x / (curve 0 - curve x))
      (𝓝[>] 0) (𝓝 value) := by
  obtain ⟨value, limit⟩ := contourCauchy_symmetric_limit_exists radius_pos holder_nonneg
    chord_pos differentiable tangent_continuous holder_bound chord_bound
  refine ⟨value, limit.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT radius_pos] with cutoff cutoff_mem
  have curve_continuous : ContinuousOn curve (Icc (-radius) radius) := by
    intro x hx
    exact (differentiable x hx).continuousAt.continuousWithinAt
  have kernel_continuous : ContinuousOn (fun x => tangent x / (curve 0 - curve x))
      (Icc (-radius) radius \ {0}) := by
    apply (tangent_continuous.mono diff_subset).div
      (continuousOn_const.sub (curve_continuous.mono diff_subset))
    intro x hx equal
    have x_ne : x ≠ 0 := by simpa using hx.2
    have zero_norm : ‖curve x - curve 0‖ = 0 := by
      rw [sub_eq_zero.mp equal, sub_self, norm_zero]
    have bound := chord_bound x hx.1
    rw [zero_norm] at bound
    exact (not_le_of_gt (mul_pos chord_pos (abs_pos.mpr x_ne))) bound
  have positive_continuous : ContinuousOn (fun x => tangent x / (curve 0 - curve x))
      (Icc cutoff radius) := by
    apply kernel_continuous.mono
    intro x hx
    exact ⟨⟨by linarith [hx.1, cutoff_mem.1], hx.2⟩,
      by simp only [mem_singleton_iff]; linarith [hx.1, cutoff_mem.1]⟩
  have negative_continuous : ContinuousOn
      (fun x => tangent (-x) / (curve 0 - curve (-x))) (Icc cutoff radius) := by
    apply kernel_continuous.comp continuousOn_neg
    intro x hx
    refine ⟨⟨by linarith [hx.2], by linarith [hx.1, cutoff_mem.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [hx.1, cutoff_mem.1]
  rw [intervalIntegral.integral_add
    (positive_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le)
    (negative_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le)]
  rw [intervalIntegral.integral_comp_neg (fun x => tangent x / (curve 0 - curve x))]
  exact add_comm _ _

noncomputable def contourVelocity (curve tangent : ℝ → ℂ) (target lower upper : ℝ) : ℂ :=
  -(1 / (2 * Real.pi)) •
    ∫ source in lower..upper, Real.log ‖curve target - curve source‖ • tangent source

theorem log_norm_contour_bound {curve : ℝ → ℂ} {x chord speed : ℝ}
    (x_pos : 0 < x) (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (chord_bound : chord * x ≤ ‖curve 0 - curve x‖)
    (speed_bound : ‖curve 0 - curve x‖ ≤ speed * x) :
    |Real.log ‖curve 0 - curve x‖| ≤
      |Real.log x| + |Real.log chord| + |Real.log speed| := by
  have positive : 0 < ‖curve 0 - curve x‖ := (mul_pos chord_pos x_pos).trans_le chord_bound
  have lower := Real.log_le_log (mul_pos chord_pos x_pos) chord_bound
  have upper := Real.log_le_log positive speed_bound
  rw [Real.log_mul chord_pos.ne' x_pos.ne'] at lower
  rw [Real.log_mul speed_pos.ne' x_pos.ne'] at upper
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log x), neg_abs_le (Real.log chord),
      abs_nonneg (Real.log speed)]
  · linarith [le_abs_self (Real.log x), le_abs_self (Real.log speed),
      abs_nonneg (Real.log chord)]

theorem contourVelocity_integrable_right {curve tangent : ℝ → ℂ}
    {radius chord speed tangentBound : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (curve_continuous : ContinuousOn curve (Icc 0 radius))
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve 0 - curve x‖)
    (speed_bound : ∀ x ∈ Ioc 0 radius, ‖curve 0 - curve x‖ ≤ speed * x)
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ tangentBound) :
    IntervalIntegrable (fun x => Real.log ‖curve 0 - curve x‖ • tangent x)
      volume 0 radius := by
  have log_integrable : IntegrableOn (fun x : ℝ => |Real.log x|) (Ioo 0 radius) := by
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le radius_pos.le).mp
      intervalIntegral.intervalIntegrable_log').norm
  have majorant_integrable : IntegrableOn (fun x : ℝ =>
      (|Real.log x| + |Real.log chord| + |Real.log speed|) * tangentBound)
      (Ioo 0 radius) := by
    have finite : volume (Ioo (0 : ℝ) radius) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    exact ((log_integrable.add (integrableOn_const.2 (Or.inr finite))).add
      (integrableOn_const.2 (Or.inr finite))).mul_const tangentBound
  have log_continuous : ContinuousOn (fun x => Real.log ‖curve 0 - curve x‖)
      (Ioo 0 radius) := by
    apply (continuousOn_const.sub (curve_continuous.mono Ioo_subset_Icc_self)).norm.log
    intro x hx
    exact ne_of_gt ((mul_pos chord_pos hx.1).trans_le (chord_bound x ⟨hx.1, hx.2.le⟩))
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le radius_pos.le]
  apply majorant_integrable.mono'
    ((log_continuous.smul (tangent_continuous.mono Ioo_subset_Icc_self)).aestronglyMeasurable
      measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul
    (log_norm_contour_bound hx.1 chord_pos speed_pos
      (chord_bound x ⟨hx.1, hx.2.le⟩) (speed_bound x ⟨hx.1, hx.2.le⟩))
    (tangent_bound x ⟨hx.1.le, hx.2.le⟩) (norm_nonneg _) (by positivity)

theorem log_lipschitz_on_positive_ray {lower first second : ℝ}
    (lower_pos : 0 < lower) (first_lower : lower ≤ first) (second_lower : lower ≤ second) :
    |Real.log first - Real.log second| ≤ |first - second| / lower := by
  have estimate := (convex_Ici lower).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (lower_pos.trans_le hx))).hasDerivWithinAt)
    (C := lower⁻¹) (fun x hx => by
      rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lower_pos.trans_le hx)]
      exact inv_anti₀ lower_pos hx) second_lower first_lower
  simpa only [Real.norm_eq_abs, div_eq_mul_inv, mul_comm] using estimate

theorem log_norm_contour_difference {first second : ℝ → ℂ} {x chord difference : ℝ}
    (x_pos : 0 < x) (chord_pos : 0 < chord)
    (first_chord : chord * x ≤ ‖first 0 - first x‖)
    (second_chord : chord * x ≤ ‖second 0 - second x‖)
    (increment_difference : ‖(first 0 - first x) - (second 0 - second x)‖ ≤ difference * x) :
    |Real.log ‖first 0 - first x‖ - Real.log ‖second 0 - second x‖| ≤
      difference / chord := by
  calc
    _ ≤ |‖first 0 - first x‖ - ‖second 0 - second x‖| / (chord * x) :=
      log_lipschitz_on_positive_ray (mul_pos chord_pos x_pos) first_chord second_chord
    _ ≤ (difference * x) / (chord * x) := by
      apply div_le_div_of_nonneg_right _ (mul_pos chord_pos x_pos).le
      exact (abs_norm_sub_norm_le _ _).trans increment_difference
    _ = _ := by field_simp; ring

theorem contour_increment_difference {first second firstTangent secondTangent : ℝ → ℂ}
    {x difference : ℝ} (x_nonneg : 0 ≤ x)
    (first_derivative : ∀ y ∈ Icc 0 x, HasDerivAt first (firstTangent y) y)
    (second_derivative : ∀ y ∈ Icc 0 x, HasDerivAt second (secondTangent y) y)
    (tangent_difference : ∀ y ∈ Icc 0 x,
      ‖firstTangent y - secondTangent y‖ ≤ difference) :
    ‖(first 0 - first x) - (second 0 - second x)‖ ≤ difference * x := by
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => ((first_derivative y hy).sub (second_derivative y hy)).hasDerivWithinAt)
    (fun y hy => tangent_difference y ⟨hy.1, hy.2.le⟩) x (right_mem_Icc.mpr x_nonneg)
  rw [sub_zero] at estimate
  convert estimate using 1
  rw [← norm_neg]
  congr 1
  abel

theorem contour_speed_bound {curve tangent : ℝ → ℂ} {radius speed : ℝ}
    (derivative : ∀ x ∈ Icc 0 radius, HasDerivAt curve (tangent x) x)
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (x : ℝ) (x_mem : x ∈ Icc 0 radius) :
    ‖curve 0 - curve x‖ ≤ speed * x := by
  have estimate := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => (derivative y ⟨hy.1, hy.2.trans x_mem.2⟩).hasDerivWithinAt)
    (fun y hy => tangent_bound y ⟨hy.1, hy.2.le.trans x_mem.2⟩) x
    (right_mem_Icc.mpr x_mem.1)
  simpa only [norm_sub_rev, sub_zero] using estimate

theorem contourVelocity_integrand_difference {first second firstTangent secondTangent : ℝ → ℂ}
    {x chord speed difference : ℝ} (x_pos : 0 < x) (chord_pos : 0 < chord)
    (speed_pos : 0 < speed) (difference_nonneg : 0 ≤ difference)
    (first_chord : chord * x ≤ ‖first 0 - first x‖)
    (second_chord : chord * x ≤ ‖second 0 - second x‖)
    (second_speed : ‖second 0 - second x‖ ≤ speed * x)
    (first_tangent_bound : ‖firstTangent x‖ ≤ speed)
    (tangent_difference : ‖firstTangent x - secondTangent x‖ ≤ difference)
    (increment_difference : ‖(first 0 - first x) - (second 0 - second x)‖ ≤ difference * x) :
    ‖Real.log ‖first 0 - first x‖ • firstTangent x -
      Real.log ‖second 0 - second x‖ • secondTangent x‖ ≤
      difference * (speed / chord + |Real.log x| + |Real.log chord| + |Real.log speed|) := by
  have identity : Real.log ‖first 0 - first x‖ • firstTangent x -
      Real.log ‖second 0 - second x‖ • secondTangent x =
      (Real.log ‖first 0 - first x‖ - Real.log ‖second 0 - second x‖) • firstTangent x +
        Real.log ‖second 0 - second x‖ • (firstTangent x - secondTangent x) := by
    simp only [sub_smul, smul_sub]
    abel
  rw [identity]
  calc
    _ ≤ ‖(Real.log ‖first 0 - first x‖ - Real.log ‖second 0 - second x‖) • firstTangent x‖ +
        ‖Real.log ‖second 0 - second x‖ • (firstTangent x - secondTangent x)‖ := norm_add_le _ _
    _ ≤ (difference / chord) * speed +
        (|Real.log x| + |Real.log chord| + |Real.log speed|) * difference := by
      simp only [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · exact mul_le_mul
          (log_norm_contour_difference x_pos chord_pos first_chord second_chord increment_difference)
          first_tangent_bound (norm_nonneg _) (by positivity)
      · exact mul_le_mul
          (log_norm_contour_bound x_pos chord_pos speed_pos second_chord second_speed)
          tangent_difference (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem contourVelocity_lipschitz_right {first second firstTangent secondTangent : ℝ → ℂ}
    {radius chord speed difference : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed) (difference_nonneg : 0 ≤ difference)
    (first_derivative : ∀ x ∈ Icc 0 radius, HasDerivAt first (firstTangent x) x)
    (second_derivative : ∀ x ∈ Icc 0 radius, HasDerivAt second (secondTangent x) x)
    (first_tangent_continuous : ContinuousOn firstTangent (Icc 0 radius))
    (second_tangent_continuous : ContinuousOn secondTangent (Icc 0 radius))
    (first_chord : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖first 0 - first x‖)
    (second_chord : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖second 0 - second x‖)
    (first_tangent_bound : ∀ x ∈ Icc 0 radius, ‖firstTangent x‖ ≤ speed)
    (second_tangent_bound : ∀ x ∈ Icc 0 radius, ‖secondTangent x‖ ≤ speed)
    (tangent_difference : ∀ x ∈ Icc 0 radius,
      ‖firstTangent x - secondTangent x‖ ≤ difference) :
    ‖contourVelocity first firstTangent 0 0 radius -
      contourVelocity second secondTangent 0 0 radius‖ ≤
      (1 / (2 * Real.pi)) * difference *
        ∫ x in (0 : ℝ)..radius, (speed / chord + |Real.log x| + |Real.log chord| + |Real.log speed|) := by
  have first_speed := contour_speed_bound first_derivative first_tangent_bound
  have second_speed := contour_speed_bound second_derivative second_tangent_bound
  have first_continuous : ContinuousOn first (Icc 0 radius) :=
    fun x hx => (first_derivative x hx).continuousAt.continuousWithinAt
  have second_continuous : ContinuousOn second (Icc 0 radius) :=
    fun x hx => (second_derivative x hx).continuousAt.continuousWithinAt
  have first_integrable := contourVelocity_integrable_right radius_pos chord_pos speed_pos
    first_continuous first_tangent_continuous first_chord
    (fun x hx => first_speed x ⟨hx.1.le, hx.2⟩) first_tangent_bound
  have second_integrable := contourVelocity_integrable_right radius_pos chord_pos speed_pos
    second_continuous second_tangent_continuous second_chord
    (fun x hx => second_speed x ⟨hx.1.le, hx.2⟩) second_tangent_bound
  have log_integrable : IntegrableOn (fun x : ℝ => |Real.log x|) (Ioo 0 radius) :=
    ((intervalIntegrable_iff_integrableOn_Ioo_of_le radius_pos.le).mp
      intervalIntegral.intervalIntegrable_log').norm
  have finite : volume (Ioo (0 : ℝ) radius) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  have majorant_integrable : IntegrableOn (fun x : ℝ =>
      difference * (speed / chord + |Real.log x| + |Real.log chord| + |Real.log speed|))
      (Ioo 0 radius) := by
    exact (((integrableOn_const.2 (Or.inr finite)).add log_integrable).add
      (integrableOn_const.2 (Or.inr finite)) |>.add
      (integrableOn_const.2 (Or.inr finite))).const_mul difference
  have estimate := norm_integral_le_of_norm_le majorant_integrable
    (show ∀ᵐ x ∂volume.restrict (Ioo 0 radius),
      ‖Real.log ‖first 0 - first x‖ • firstTangent x -
        Real.log ‖second 0 - second x‖ • secondTangent x‖ ≤
        difference * (speed / chord + |Real.log x| + |Real.log chord| + |Real.log speed|) from by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact contourVelocity_integrand_difference hx.1 chord_pos speed_pos difference_nonneg
        (first_chord x ⟨hx.1, hx.2.le⟩) (second_chord x ⟨hx.1, hx.2.le⟩)
        (second_speed x ⟨hx.1.le, hx.2.le⟩) (first_tangent_bound x ⟨hx.1.le, hx.2.le⟩)
        (tangent_difference x ⟨hx.1.le, hx.2.le⟩)
        (contour_increment_difference hx.1.le
          (fun y hy => first_derivative y ⟨hy.1, hy.2.trans hx.2.le⟩)
          (fun y hy => second_derivative y ⟨hy.1, hy.2.trans hx.2.le⟩)
          (fun y hy => tangent_difference y ⟨hy.1, hy.2.trans hx.2.le⟩)))
  rw [integral_const_mul] at estimate
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le radius_pos.le,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le radius_pos.le] at estimate
  unfold contourVelocity
  rw [← smul_sub, norm_smul, ← intervalIntegral.integral_sub first_integrable second_integrable]
  have coefficient : ‖(-(1 / (2 * Real.pi)) : ℝ)‖ = 1 / (2 * Real.pi) := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  rw [coefficient]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (difference *
        ∫ x in (0 : ℝ)..radius, (speed / chord + |Real.log x| + |Real.log chord| + |Real.log speed|)) :=
      mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = _ := by ring

theorem contour_log_kernel_derivative {curve : ℝ → ℂ} {tangent : ℂ} {target source : ℝ}
    (derivative : HasDerivAt curve tangent target) (separated : curve target - curve source ≠ 0) :
    HasDerivAt (fun x => Real.log ‖curve x - curve source‖)
      ((@inner ℝ ℂ _ (curve target - curve source) tangent) /
        ‖curve target - curve source‖ ^ 2) target := by
  have square_derivative := (derivative.sub_const (curve source)).norm_sq
  have log_derivative := (square_derivative.log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr separated))).div_const 2
  convert log_derivative using 1
  · funext x
    rw [Real.log_pow]
    simp
  · ring

noncomputable def contourCauchyDensityRemainder (curve tangent density : ℝ → ℂ)
    (target source : ℝ) : ℂ :=
  (density source - density target) * tangent source / (curve target - curve source)

theorem contourCauchyDensityRemainder_bound {curve tangent density : ℝ → ℂ}
    {x holder speed chord : ℝ} (x_pos : 0 < x) (holder_nonneg : 0 ≤ holder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (density_bound : ‖density x - density 0‖ ≤ holder * Real.sqrt x)
    (tangent_bound : ‖tangent x‖ ≤ speed)
    (chord_bound : chord * x ≤ ‖curve 0 - curve x‖) :
    ‖contourCauchyDensityRemainder curve tangent density 0 x‖ ≤
      (holder * speed / chord) / Real.sqrt x := by
  have sqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr x_pos
  have numerator_nonneg : 0 ≤ holder * Real.sqrt x * speed := by positivity
  simp only [contourCauchyDensityRemainder, norm_div, norm_mul]
  calc
    _ ≤ (holder * Real.sqrt x * speed) / ‖curve 0 - curve x‖ :=
      div_le_div_of_nonneg_right
        (mul_le_mul density_bound tangent_bound (norm_nonneg _) (by positivity)) (norm_nonneg _)
    _ ≤ (holder * Real.sqrt x * speed) / (chord * x) :=
      div_le_div_of_nonneg_left numerator_nonneg (mul_pos chord_pos x_pos) chord_bound
    _ = _ := by
      field_simp
      calc
        _ = holder * speed * chord * (Real.sqrt x ^ 2) := by ring
        _ = _ := by rw [Real.sq_sqrt x_pos.le]; ring

theorem contourCauchyDensityRemainder_integrable {curve tangent density : ℝ → ℂ}
    {radius holder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (curve_continuous : ContinuousOn curve (Icc 0 radius))
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (density_continuous : ContinuousOn density (Icc 0 radius))
    (density_bound : ∀ x ∈ Ioc 0 radius, ‖density x - density 0‖ ≤ holder * Real.sqrt x)
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve 0 - curve x‖) :
    IntegrableOn (contourCauchyDensityRemainder curve tangent density 0) (Ioo 0 radius) := by
  have continuous : ContinuousOn (contourCauchyDensityRemainder curve tangent density 0)
      (Ioo 0 radius) := by
    change ContinuousOn (fun x => (density x - density 0) * tangent x /
      (curve 0 - curve x)) (Ioo 0 radius)
    apply ((density_continuous.mono Ioo_subset_Icc_self).sub continuousOn_const |>.mul
      (tangent_continuous.mono Ioo_subset_Icc_self)).div
      (continuousOn_const.sub (curve_continuous.mono Ioo_subset_Icc_self))
    intro x hx
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos hx.1).trans_le
      (chord_bound x ⟨hx.1, hx.2.le⟩)))
  have majorant : IntegrableOn (fun x : ℝ => (holder * speed / chord) * x ^ (-(1 / 2 : ℝ)))
      (Ioo 0 radius) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff radius_pos).2 (by norm_num)).const_mul _
  apply majorant.mono' (continuous.aestronglyMeasurable measurableSet_Ioo)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have estimate := contourCauchyDensityRemainder_bound hx.1 holder_nonneg speed_nonneg chord_pos
    (density_bound x ⟨hx.1, hx.2.le⟩) (tangent_bound x ⟨hx.1.le, hx.2.le⟩)
    (chord_bound x ⟨hx.1, hx.2.le⟩)
  rw [Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv] using estimate

theorem contourCauchyDensityRemainder_integral_bound {curve tangent density : ℝ → ℂ}
    {radius holder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (density_bound : ∀ x ∈ Ioc 0 radius, ‖density x - density 0‖ ≤ holder * Real.sqrt x)
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve 0 - curve x‖) :
    ‖∫ x in Ioo 0 radius, contourCauchyDensityRemainder curve tangent density 0 x‖ ≤
      2 * (holder * speed / chord) * Real.sqrt radius := by
  apply integral_norm_le_inv_sqrt radius_pos
  intro x hx
  exact contourCauchyDensityRemainder_bound hx.1 holder_nonneg speed_nonneg chord_pos
    (density_bound x ⟨hx.1, hx.2.le⟩) (tangent_bound x ⟨hx.1.le, hx.2.le⟩)
    (chord_bound x ⟨hx.1, hx.2.le⟩)

noncomputable def contourCauchyKernel (curve tangent : ℝ → ℂ) (target source : ℝ) : ℂ :=
  tangent source / (curve target - curve source)

theorem contourCauchyKernel_size {curve tangent : ℝ → ℂ} {target source speed chord : ℝ}
    (distinct : target ≠ source) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (tangent_bound : ‖tangent source‖ ≤ speed)
    (chord_bound : chord * |target - source| ≤ ‖curve target - curve source‖) :
    ‖contourCauchyKernel curve tangent target source‖ ≤ (speed / chord) / |target - source| := by
  have distance_pos : 0 < |target - source| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  simp only [contourCauchyKernel, norm_div]
  calc
    _ ≤ speed / ‖curve target - curve source‖ :=
      div_le_div_of_nonneg_right tangent_bound (norm_nonneg _)
    _ ≤ speed / (chord * |target - source|) :=
      div_le_div_of_nonneg_left speed_nonneg (mul_pos chord_pos distance_pos) chord_bound
    _ = _ := by ring

theorem contourCauchyKernel_difference_norm {curve tangent : ℝ → ℂ} {first second source : ℝ}
    (first_separated : curve first - curve source ≠ 0)
    (second_separated : curve second - curve source ≠ 0) :
    ‖contourCauchyKernel curve tangent first source -
      contourCauchyKernel curve tangent second source‖ =
      ‖tangent source‖ * ‖curve first - curve second‖ /
        (‖curve first - curve source‖ * ‖curve second - curve source‖) := by
  simp only [contourCauchyKernel, div_eq_mul_inv, ← mul_sub, norm_mul]
  have inverse_difference := dist_inv_inv₀ first_separated second_separated
  simp only [dist_eq_norm] at inverse_difference
  rw [inverse_difference]
  have difference : (curve first - curve source) - (curve second - curve source) =
      curve first - curve second := by abel
  rw [difference]
  ring

theorem contourCauchyKernel_far_difference {curve tangent : ℝ → ℂ}
    {first second source speed chord : ℝ} (first_distinct : first ≠ source)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (nearby : |first - second| ≤ |first - source| / 2)
    (tangent_bound : ‖tangent source‖ ≤ speed)
    (target_lipschitz : ‖curve first - curve second‖ ≤ speed * |first - second|)
    (first_chord : chord * |first - source| ≤ ‖curve first - curve source‖)
    (second_chord : chord * |second - source| ≤ ‖curve second - curve source‖) :
    ‖contourCauchyKernel curve tangent first source -
      contourCauchyKernel curve tangent second source‖ ≤
      (2 * speed ^ 2 / chord ^ 2) * |first - second| / |first - source| ^ 2 := by
  have distance_pos : 0 < |first - source| := abs_pos.mpr (sub_ne_zero.mpr first_distinct)
  have triangle : |first - source| ≤ |first - second| + |second - source| := by
    convert abs_add (first - second) (second - source) using 1; congr 1; ring
  have second_distance : |first - source| / 2 ≤ |second - source| := by linarith
  have second_distance_pos : 0 < |second - source| := by linarith
  have first_norm_pos := (mul_pos chord_pos distance_pos).trans_le first_chord
  have second_norm_pos := (mul_pos chord_pos second_distance_pos).trans_le second_chord
  rw [contourCauchyKernel_difference_norm (norm_ne_zero_iff.mp first_norm_pos.ne')
    (norm_ne_zero_iff.mp second_norm_pos.ne')]
  apply (div_le_iff₀ (mul_pos first_norm_pos second_norm_pos)).mpr
  calc
    _ ≤ speed * (speed * |first - second|) :=
      mul_le_mul tangent_bound target_lipschitz (norm_nonneg _) speed_nonneg
    _ = ((2 * speed ^ 2 / chord ^ 2) * |first - second| / |first - source| ^ 2) *
        ((chord * |first - source|) * (chord * (|first - source| / 2))) := by
      have algebra : ∀ distance jump : ℝ, 0 < distance →
          speed * (speed * jump) =
            ((2 * speed ^ 2 / chord ^ 2) * jump / distance ^ 2) *
              ((chord * distance) * (chord * (distance / 2))) := by
        intro distance jump positive
        field_simp [chord_pos.ne', positive.ne']
        ring
      exact algebra _ _ distance_pos
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul first_chord
        ((mul_le_mul_of_nonneg_left second_distance chord_pos.le).trans second_chord)
        (by positivity) (norm_nonneg _)

theorem contourCauchy_far_majorant_integral {cutoff radius : ℝ} (cutoff_pos : 0 < cutoff)
    (ordered : cutoff ≤ radius) :
    (∫ x in cutoff..radius, cutoff * x ^ (-(3 / 2 : ℝ))) ≤ 2 * Real.sqrt cutoff := by
  have radius_pos : 0 < radius := cutoff_pos.trans_le ordered
  have zero_not_mem : (0 : ℝ) ∉ uIcc cutoff radius := by
    rw [uIcc_of_le ordered]
    intro h
    exact (not_le_of_gt cutoff_pos) h.1
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by norm_num, zero_not_mem⟩)]
  norm_num
  rw [Real.rpow_neg radius_pos.le, Real.rpow_neg cutoff_pos.le,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have identity : cutoff * (((Real.sqrt radius)⁻¹ - (Real.sqrt cutoff)⁻¹) / (-(1 / 2 : ℝ))) =
      2 * (cutoff / Real.sqrt cutoff) - 2 * cutoff / Real.sqrt radius := by ring
  rw [identity, Real.div_sqrt]
  exact sub_le_self _ (by positivity)

theorem contour_log_kernel_derivative_cauchy {curve : ℝ → ℂ} {tangent : ℂ}
    {target source : ℝ} (derivative : HasDerivAt curve tangent target)
    (separated : curve target - curve source ≠ 0) :
    HasDerivAt (fun x => Real.log ‖curve x - curve source‖)
      (tangent / (curve target - curve source)).re target := by
  convert contour_log_kernel_derivative derivative separated using 1
  rw [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.div_re, Complex.normSq_eq_norm_sq]
  ring

theorem principal_value_of_symmetric_integrable {kernel : ℝ → ℂ} {radius : ℝ}
    (radius_pos : 0 < radius)
    (kernel_continuous : ContinuousOn kernel (Icc (-radius) radius \ {0}))
    (symmetric_integrable : IntegrableOn (fun x => kernel x + kernel (-x)) (Ioo 0 radius)) :
    ∃ value : ℂ, Tendsto (fun cutoff : ℝ =>
      (∫ x in (-radius)..(-cutoff), kernel x) + ∫ x in cutoff..radius, kernel x)
      (𝓝[>] 0) (𝓝 value) := by
  have integrable_closed : IntegrableOn (fun x => kernel x + kernel (-x)) (uIcc 0 radius) := by
    rw [uIcc_of_le radius_pos.le, integrableOn_Icc_iff_integrableOn_Ioo]
    exact symmetric_integrable
  have continuous := intervalIntegral.continuousOn_primitive_interval_left integrable_closed
  have limit := continuous 0 (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 radius)
  rw [ContinuousWithinAt, uIcc_of_le radius_pos.le,
    nhdsWithin_Icc_eq_nhdsGE radius_pos] at limit
  refine ⟨_, (limit.mono_left (nhdsWithin_mono 0 Ioi_subset_Ici_self)).congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsGT radius_pos] with cutoff cutoff_mem
  have positive_continuous : ContinuousOn kernel (Icc cutoff radius) := by
    apply kernel_continuous.mono
    intro x hx
    exact ⟨⟨by linarith [hx.1, cutoff_mem.1], hx.2⟩,
      by simp only [mem_singleton_iff]; linarith [hx.1, cutoff_mem.1]⟩
  have negative_continuous : ContinuousOn (fun x => kernel (-x)) (Icc cutoff radius) := by
    apply kernel_continuous.comp continuousOn_neg
    intro x hx
    refine ⟨⟨by linarith [hx.2], by linarith [hx.1, cutoff_mem.1]⟩, ?_⟩
    simp only [mem_singleton_iff]
    linarith [hx.1, cutoff_mem.1]
  rw [intervalIntegral.integral_add
    (positive_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le)
    (negative_continuous.intervalIntegrable_of_Icc cutoff_mem.2.le),
    intervalIntegral.integral_comp_neg kernel]
  exact add_comm _ _

theorem contourCauchy_weighted_symmetric_integrable {curve tangent density : ℝ → ℂ}
    {radius holder densityHolder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (densityHolder_nonneg : 0 ≤ densityHolder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (density_continuous : ContinuousOn density (Icc (-radius) radius))
    (tangent_holder : ∀ x ∈ Icc (-radius) radius, ∀ y ∈ Icc (-radius) radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (density_holder : ∀ x ∈ Icc (-radius) radius,
      ‖density x - density 0‖ ≤ densityHolder * Real.sqrt |x|)
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖) :
    IntegrableOn (fun x => density x * contourCauchyKernel curve tangent 0 x +
      density (-x) * contourCauchyKernel curve tangent 0 (-x)) (Ioo 0 radius) := by
  have right_mem : ∀ x ∈ Icc 0 radius, x ∈ Icc (-radius) radius := by
    intro x hx
    exact ⟨(neg_nonpos.mpr radius_pos.le).trans hx.1, hx.2⟩
  have left_mem : ∀ x ∈ Icc 0 radius, -x ∈ Icc (-radius) radius := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have curve_continuous : ContinuousOn curve (Icc (-radius) radius) :=
    fun x hx => (derivative x hx).continuousAt.continuousWithinAt
  have right_integrable := contourCauchyDensityRemainder_integrable radius_pos densityHolder_nonneg
    speed_nonneg chord_pos (curve_continuous.mono (by intro x hx; exact right_mem x hx))
    (tangent_continuous.mono (by intro x hx; exact right_mem x hx))
    (density_continuous.mono (by intro x hx; exact right_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (density_holder x (right_mem x ⟨hx.1.le, hx.2⟩)))
    (fun x hx => tangent_bound x (right_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
      (chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))
  have left_integrable := contourCauchyDensityRemainder_integrable
    (curve := fun x => curve (-x)) (tangent := fun x => -tangent (-x))
    (density := fun x => density (-x)) radius_pos densityHolder_nonneg speed_nonneg chord_pos
    (curve_continuous.comp continuousOn_neg (fun x hx => left_mem x hx))
    ((tangent_continuous.comp continuousOn_neg (fun x hx => left_mem x hx)).neg)
    (density_continuous.comp continuousOn_neg (fun x hx => left_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (density_holder (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
    (fun x hx => by simpa using tangent_bound (-x) (left_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
      (chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
  have constants_integrable :=
    (contourCauchy_symmetric_integrable radius_pos holder_nonneg chord_pos derivative
      tangent_continuous tangent_holder chord_bound).const_mul (density 0)
  have combined : IntegrableOn (fun x =>
      contourCauchyDensityRemainder curve tangent density 0 x -
        contourCauchyDensityRemainder (fun y => curve (-y)) (fun y => -tangent (-y))
          (fun y => density (-y)) 0 x +
        density 0 * (tangent x / (curve 0 - curve x) + tangent (-x) / (curve 0 - curve (-x))))
      (Ioo 0 radius) := (right_integrable.sub left_integrable).add constants_integrable
  apply combined.congr_fun _ measurableSet_Ioo
  intro x hx
  simp only [contourCauchyDensityRemainder, contourCauchyKernel, neg_zero, neg_div]
  ring

theorem contourCauchy_weighted_principal_value_exists {curve tangent density : ℝ → ℂ}
    {radius holder densityHolder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (densityHolder_nonneg : 0 ≤ densityHolder)
    (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (density_continuous : ContinuousOn density (Icc (-radius) radius))
    (tangent_holder : ∀ x ∈ Icc (-radius) radius, ∀ y ∈ Icc (-radius) radius,
      ‖tangent x - tangent y‖ ≤ holder * Real.sqrt |y - x|)
    (density_holder : ∀ x ∈ Icc (-radius) radius,
      ‖density x - density 0‖ ≤ densityHolder * Real.sqrt |x|)
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖) :
    ∃ value : ℂ, Tendsto (fun cutoff : ℝ =>
      (∫ x in (-radius)..(-cutoff), density x * contourCauchyKernel curve tangent 0 x) +
        ∫ x in cutoff..radius, density x * contourCauchyKernel curve tangent 0 x)
      (𝓝[>] 0) (𝓝 value) := by
  apply principal_value_of_symmetric_integrable radius_pos
  · have curve_continuous : ContinuousOn curve (Icc (-radius) radius) :=
      fun x hx => (derivative x hx).continuousAt.continuousWithinAt
    have kernel_continuous : ContinuousOn (contourCauchyKernel curve tangent 0)
        (Icc (-radius) radius \ {0}) := by
      change ContinuousOn (fun x => tangent x / (curve 0 - curve x))
        (Icc (-radius) radius \ {0})
      apply (tangent_continuous.mono diff_subset).div
        (continuousOn_const.sub (curve_continuous.mono diff_subset))
      intro x hx equal
      have x_ne : x ≠ 0 := by simpa using hx.2
      have zero_norm : ‖curve x - curve 0‖ = 0 := by
        rw [sub_eq_zero.mp equal, sub_self, norm_zero]
      have bound := chord_bound x hx.1
      rw [zero_norm] at bound
      exact (not_le_of_gt (mul_pos chord_pos (abs_pos.mpr x_ne))) bound
    exact (density_continuous.mono diff_subset).mul kernel_continuous
  · exact contourCauchy_weighted_symmetric_integrable radius_pos holder_nonneg densityHolder_nonneg
      speed_nonneg chord_pos derivative tangent_continuous density_continuous tangent_holder
      density_holder tangent_bound chord_bound

theorem contourEvaluationCauchy_remainder_bound {curve tangent : ℝ → ℂ}
    {x holder chord : ℝ} (x_pos : 0 < x) (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ y ∈ Icc 0 x, HasDerivAt curve (tangent y) y)
    (holder_bound : ∀ y ∈ Icc 0 x, ‖tangent y - tangent 0‖ ≤ holder * Real.sqrt y)
    (chord_bound : chord * x ≤ ‖curve 0 - curve x‖) :
    ‖tangent 0 / (curve 0 - curve x) + (x : ℂ)⁻¹‖ ≤
      (holder / chord) / Real.sqrt x := by
  have derivative_bound : ∀ y ∈ Ico 0 x,
      ‖tangent y - tangent 0‖ ≤ holder * Real.sqrt x := by
    intro y hy
    exact (holder_bound y ⟨hy.1, hy.2.le⟩).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hy.2.le) holder_nonneg)
  have remainder := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun y hy => ((derivative y hy).sub ((hasDerivAt_id y).smul_const (tangent 0))).hasDerivWithinAt)
    (by simpa only [one_smul] using derivative_bound) x (right_mem_Icc.mpr x_pos.le)
  have numerator : ‖curve 0 - curve x + x • tangent 0‖ ≤ holder * Real.sqrt x * x := by
    simp only [id_eq, zero_smul, sub_zero] at remainder
    convert remainder using 1
    rw [← norm_neg]
    congr 1
    abel
  have norm_positive := (mul_pos chord_pos x_pos).trans_le chord_bound
  have curve_ne := norm_ne_zero_iff.mp norm_positive.ne'
  have cast_ne : (x : ℂ) ≠ 0 := by exact_mod_cast x_pos.ne'
  have identity : tangent 0 / (curve 0 - curve x) + (x : ℂ)⁻¹ =
      (curve 0 - curve x + x • tangent 0) / ((curve 0 - curve x) * (x : ℂ)) := by
    rw [Complex.real_smul]
    field_simp
    ring
  rw [identity, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos x_pos]
  apply (div_le_iff₀ (mul_pos norm_positive x_pos)).mpr
  calc
    _ ≤ holder * Real.sqrt x * x := numerator
    _ = ((holder / chord) / Real.sqrt x) * (chord * x * x) := by
      field_simp
      calc
        _ = holder * chord * (Real.sqrt x ^ 2) * x := by ring
        _ = _ := by rw [Real.sq_sqrt x_pos.le]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right chord_bound x_pos.le) (by positivity)

noncomputable def contourVelocityDerivativeKernel (curve tangent : ℝ → ℂ)
    (target source : ℝ) : ℂ :=
  (tangent target / (curve target - curve source)).re • tangent source

theorem contourVelocityDerivativeKernel_remainder_bound {curve tangent : ℝ → ℂ}
    {x holder speed chord : ℝ} (x_pos : 0 < x) (holder_nonneg : 0 ≤ holder)
    (chord_pos : 0 < chord)
    (derivative : ∀ y ∈ Icc 0 x, HasDerivAt curve (tangent y) y)
    (holder_bound : ∀ y ∈ Icc 0 x, ‖tangent y - tangent 0‖ ≤ holder * Real.sqrt y)
    (tangent_bound : ‖tangent x‖ ≤ speed)
    (chord_bound : chord * x ≤ ‖curve 0 - curve x‖) :
    ‖contourVelocityDerivativeKernel curve tangent 0 x + x⁻¹ • tangent 0‖ ≤
      (holder * speed / chord + holder) / Real.sqrt x := by
  have inverse_bound := contourEvaluationCauchy_remainder_bound x_pos holder_nonneg chord_pos
    derivative holder_bound chord_bound
  have identity : contourVelocityDerivativeKernel curve tangent 0 x + x⁻¹ • tangent 0 =
      (tangent 0 / (curve 0 - curve x) + (x : ℂ)⁻¹).re • tangent x +
        x⁻¹ • (tangent 0 - tangent x) := by
    simp only [contourVelocityDerivativeKernel, Complex.add_re, ← Complex.ofReal_inv,
      Complex.ofReal_re, add_smul, smul_sub]
    abel
  rw [identity]
  calc
    _ ≤ ‖(tangent 0 / (curve 0 - curve x) + (x : ℂ)⁻¹).re • tangent x‖ +
        ‖x⁻¹ • (tangent 0 - tangent x)‖ := norm_add_le _ _
    _ ≤ ((holder / chord) / Real.sqrt x) * speed + x⁻¹ * (holder * Real.sqrt x) := by
      simp only [norm_smul, Real.norm_eq_abs]
      apply add_le_add
      · exact mul_le_mul ((Complex.abs_re_le_norm _).trans inverse_bound) tangent_bound
          (norm_nonneg _) (by positivity)
      · rw [abs_inv, abs_of_pos x_pos, norm_sub_rev]
        exact mul_le_mul_of_nonneg_left (holder_bound x (right_mem_Icc.mpr x_pos.le)) (by positivity)
    _ = _ := by
      rw [show x⁻¹ * (holder * Real.sqrt x) = holder * (Real.sqrt x / x) by ring,
        Real.sqrt_div_self]
      ring

theorem integrableOn_of_inv_sqrt_bound {integrand : ℝ → ℂ} {radius bound : ℝ}
    (radius_pos : 0 < radius)
    (measurable : AEStronglyMeasurable integrand (volume.restrict (Ioo 0 radius)))
    (majorized : ∀ x ∈ Ioo 0 radius, ‖integrand x‖ ≤ bound / Real.sqrt x) :
    IntegrableOn integrand (Ioo 0 radius) := by
  have majorant : IntegrableOn (fun x : ℝ => bound * x ^ (-(1 / 2 : ℝ)))
      (Ioo 0 radius) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff radius_pos).2 (by norm_num)).const_mul _
  apply majorant.mono' measurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  rw [Real.rpow_neg hx.1.le, ← Real.sqrt_eq_rpow]
  simpa only [div_eq_mul_inv] using majorized x hx

theorem contourVelocityDerivativeKernel_continuousOn {curve tangent : ℝ → ℂ}
    {domain : Set ℝ} {target : ℝ} (curve_continuous : ContinuousOn curve domain)
    (tangent_continuous : ContinuousOn tangent domain)
    (separated : ∀ x ∈ domain, curve target - curve x ≠ 0) :
    ContinuousOn (contourVelocityDerivativeKernel curve tangent target) domain := by
  exact (Complex.continuous_re.comp_continuousOn
    (continuousOn_const.div (continuousOn_const.sub curve_continuous) separated)).smul
      tangent_continuous

theorem contourVelocityDerivativeKernel_remainder_integrable {curve tangent : ℝ → ℂ}
    {radius holder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ Icc 0 radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (holder_bound : ∀ x ∈ Icc 0 radius, ‖tangent x - tangent 0‖ ≤ holder * Real.sqrt x)
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve 0 - curve x‖) :
    IntegrableOn (fun x => contourVelocityDerivativeKernel curve tangent 0 x + x⁻¹ • tangent 0)
      (Ioo 0 radius) := by
  have curve_continuous : ContinuousOn curve (Icc 0 radius) :=
    fun x hx => (derivative x hx).continuousAt.continuousWithinAt
  have kernel_continuous := contourVelocityDerivativeKernel_continuousOn
    (curve_continuous.mono Ioo_subset_Icc_self) (tangent_continuous.mono Ioo_subset_Icc_self)
    (target := 0) (fun x hx => norm_ne_zero_iff.mp
      (ne_of_gt ((mul_pos chord_pos hx.1).trans_le (chord_bound x ⟨hx.1, hx.2.le⟩))))
  have inverse_continuous : ContinuousOn (fun x : ℝ => x⁻¹) (Ioo 0 radius) :=
    continuousOn_id.inv₀ (fun x hx => hx.1.ne')
  apply integrableOn_of_inv_sqrt_bound radius_pos
    ((kernel_continuous.add (inverse_continuous.smul continuousOn_const)).aestronglyMeasurable
      measurableSet_Ioo)
  intro x hx
  exact contourVelocityDerivativeKernel_remainder_bound hx.1 holder_nonneg chord_pos
    (fun y hy => derivative y ⟨hy.1, hy.2.trans hx.2.le⟩)
    (fun y hy => holder_bound y ⟨hy.1, hy.2.trans hx.2.le⟩)
    (tangent_bound x ⟨hx.1.le, hx.2.le⟩) (chord_bound x ⟨hx.1, hx.2.le⟩)

theorem contourVelocityDerivativeKernel_reflect (curve tangent : ℝ → ℂ) (x : ℝ) :
    contourVelocityDerivativeKernel (fun y => curve (-y)) (fun y => -tangent (-y)) 0 x =
      contourVelocityDerivativeKernel curve tangent 0 (-x) := by
  simp [contourVelocityDerivativeKernel, neg_div, neg_smul]

theorem contourVelocityDerivativeKernel_symmetric_integrable {curve tangent : ℝ → ℂ}
    {radius holder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ x ∈ Icc (-radius) radius,
      ‖tangent x - tangent 0‖ ≤ holder * Real.sqrt |x|)
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖) :
    IntegrableOn (fun x => contourVelocityDerivativeKernel curve tangent 0 x +
      contourVelocityDerivativeKernel curve tangent 0 (-x)) (Ioo 0 radius) := by
  have right_mem : ∀ x ∈ Icc 0 radius, x ∈ Icc (-radius) radius := by
    intro x hx
    exact ⟨(neg_nonpos.mpr radius_pos.le).trans hx.1, hx.2⟩
  have left_mem : ∀ x ∈ Icc 0 radius, -x ∈ Icc (-radius) radius := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have right_integrable := contourVelocityDerivativeKernel_remainder_integrable radius_pos
    holder_nonneg chord_pos (fun x hx => derivative x (right_mem x hx))
    (tangent_continuous.mono (by intro x hx; exact right_mem x hx))
    (fun x hx => by simpa [abs_of_nonneg hx.1] using holder_bound x (right_mem x hx))
    (fun x hx => tangent_bound x (right_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
      (chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))
  have left_integrable := contourVelocityDerivativeKernel_remainder_integrable
    (curve := fun x => curve (-x)) (tangent := fun x => -tangent (-x)) radius_pos
    holder_nonneg chord_pos
    (fun x hx => by
      convert (derivative (-x) (left_mem x hx)).scomp x (hasDerivAt_id x).neg using 1
      simp)
    ((tangent_continuous.comp continuousOn_neg (fun x hx => left_mem x hx)).neg)
    (fun x hx => by
      simpa only [neg_zero, neg_sub_neg, norm_sub_rev, abs_neg, abs_of_nonneg hx.1] using
        holder_bound (-x) (left_mem x hx))
    (fun x hx => by simpa using tangent_bound (-x) (left_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
      (chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
  have combined : IntegrableOn (fun x =>
      (contourVelocityDerivativeKernel curve tangent 0 x + x⁻¹ • tangent 0) +
        (contourVelocityDerivativeKernel (fun y => curve (-y)) (fun y => -tangent (-y)) 0 x +
          x⁻¹ • (-tangent (-0)))) (Ioo 0 radius) := right_integrable.add left_integrable
  apply combined.congr_fun _ measurableSet_Ioo
  intro x hx
  dsimp only
  rw [contourVelocityDerivativeKernel_reflect]
  simp only [neg_zero, smul_neg]
  abel

theorem contourVelocityDerivativeKernel_principal_value_exists {curve tangent : ℝ → ℂ}
    {radius holder speed chord : ℝ} (radius_pos : 0 < radius)
    (holder_nonneg : 0 ≤ holder) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (holder_bound : ∀ x ∈ Icc (-radius) radius,
      ‖tangent x - tangent 0‖ ≤ holder * Real.sqrt |x|)
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖) :
    ∃ value : ℂ, Tendsto (fun cutoff : ℝ =>
      (∫ x in (-radius)..(-cutoff), contourVelocityDerivativeKernel curve tangent 0 x) +
        ∫ x in cutoff..radius, contourVelocityDerivativeKernel curve tangent 0 x)
      (𝓝[>] 0) (𝓝 value) := by
  apply principal_value_of_symmetric_integrable radius_pos
  · apply contourVelocityDerivativeKernel_continuousOn
      (fun x hx => (derivative x hx.1).continuousAt.continuousWithinAt)
      (tangent_continuous.mono diff_subset)
    intro x hx equal
    have x_ne : x ≠ 0 := by simpa using hx.2
    have zero_norm : ‖curve x - curve 0‖ = 0 := by
      rw [sub_eq_zero.mp equal, sub_self, norm_zero]
    have bound := chord_bound x hx.1
    rw [zero_norm] at bound
    exact (not_le_of_gt (mul_pos chord_pos (abs_pos.mpr x_ne))) bound
  · exact contourVelocityDerivativeKernel_symmetric_integrable radius_pos holder_nonneg chord_pos
      derivative tangent_continuous holder_bound tangent_bound chord_bound

theorem contour_taylor_remainder_unordered {curve tangent : ℝ → ℂ}
    {source target holder : ℝ} (holder_nonneg : 0 ≤ holder)
    (derivative : ∀ x ∈ uIcc source target, HasDerivAt curve (tangent x) x)
    (holder_bound : ∀ x ∈ uIcc source target,
      ‖tangent x - tangent target‖ ≤ holder * Real.sqrt |x - target|) :
    ‖curve target - curve source - (target - source) • tangent target‖ ≤
      holder * Real.sqrt |target - source| * |target - source| := by
  have derivative_bound : ∀ x ∈ uIcc source target,
      ‖tangent x - tangent target‖ ≤ holder * Real.sqrt |target - source| := by
    intro x hx
    apply (holder_bound x hx).trans
    apply mul_le_mul_of_nonneg_left _ holder_nonneg
    apply Real.sqrt_le_sqrt
    simpa only [abs_sub_comm x target] using abs_sub_right_of_mem_uIcc hx
  have estimate := (convex_uIcc source target).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => ((derivative x hx).sub ((hasDerivAt_id x).smul_const
      (tangent target))).hasDerivWithinAt)
    (by simpa only [one_smul] using derivative_bound)
    left_mem_uIcc right_mem_uIcc
  simp only [id_eq, Real.norm_eq_abs] at estimate
  convert estimate using 1
  congr 1
  rw [sub_smul]
  abel

noncomputable def contourChordPhase (curve : ℝ → ℂ) (target source : ℝ) : ℂ :=
  (curve target - curve source) / star (curve target - curve source)

noncomputable def contourChordPhaseDerivative (curve tangent : ℝ → ℂ)
    (target source : ℝ) : ℂ :=
  (tangent target * star (curve target - curve source) -
    (curve target - curve source) * star (tangent target)) /
      star (curve target - curve source) ^ 2

theorem contourChordPhase_norm {curve : ℝ → ℂ} {target source : ℝ}
    (separated : curve target - curve source ≠ 0) :
    ‖contourChordPhase curve target source‖ = 1 := by
  simp only [contourChordPhase, norm_div, norm_star]
  exact div_self (norm_ne_zero_iff.mpr separated)

theorem contourChordPhase_derivative {curve : ℝ → ℂ} {tangent : ℝ → ℂ}
    {target source : ℝ} (derivative : HasDerivAt curve (tangent target) target)
    (separated : curve target - curve source ≠ 0) :
    HasDerivAt (fun x => contourChordPhase curve x source)
      (contourChordPhaseDerivative curve tangent target source) target := by
  exact (derivative.sub_const (curve source)).div
    (derivative.sub_const (curve source)).star (star_ne_zero.mpr separated)

theorem contourChordPhaseDerivative_bound {curve tangent : ℝ → ℂ}
    {source target holder speed chord : ℝ} (distinct : target ≠ source)
    (holder_nonneg : 0 ≤ holder) (speed_nonneg : 0 ≤ speed) (chord_pos : 0 < chord)
    (derivative : ∀ x ∈ uIcc source target, HasDerivAt curve (tangent x) x)
    (holder_bound : ∀ x ∈ uIcc source target,
      ‖tangent x - tangent target‖ ≤ holder * Real.sqrt |x - target|)
    (tangent_bound : ‖tangent target‖ ≤ speed)
    (chord_bound : chord * |target - source| ≤ ‖curve target - curve source‖) :
    ‖contourChordPhaseDerivative curve tangent target source‖ ≤
      (2 * speed * holder / chord ^ 2) / Real.sqrt |target - source| := by
  have distance_pos : 0 < |target - source| := abs_pos.mpr (sub_ne_zero.mpr distinct)
  have norm_positive := (mul_pos chord_pos distance_pos).trans_le chord_bound
  have remainder := contour_taylor_remainder_unordered holder_nonneg derivative holder_bound
  have numerator_identity : tangent target * star (curve target - curve source) -
      (curve target - curve source) * star (tangent target) =
      tangent target * star (curve target - curve source - (target - source) • tangent target) -
        (curve target - curve source - (target - source) • tangent target) * star (tangent target) := by
    simp [Complex.real_smul, star_sub, star_mul]
    ring
  have numerator_bound : ‖tangent target * star (curve target - curve source) -
      (curve target - curve source) * star (tangent target)‖ ≤
      2 * speed * (holder * Real.sqrt |target - source| * |target - source|) := by
    rw [numerator_identity]
    calc
      _ ≤ ‖tangent target * star (curve target - curve source - (target - source) • tangent target)‖ +
          ‖(curve target - curve source - (target - source) • tangent target) * star (tangent target)‖ :=
        norm_sub_le _ _
      _ ≤ speed * (holder * Real.sqrt |target - source| * |target - source|) +
          (holder * Real.sqrt |target - source| * |target - source|) * speed := by
        simp only [norm_mul, norm_star]
        exact add_le_add (mul_le_mul tangent_bound remainder (norm_nonneg _) speed_nonneg)
          (mul_le_mul remainder tangent_bound (norm_nonneg _) (by positivity))
      _ = _ := by ring
  simp only [contourChordPhaseDerivative, norm_div, norm_pow, norm_star]
  apply (div_le_iff₀ (sq_pos_of_pos norm_positive)).mpr
  calc
    _ ≤ 2 * speed * (holder * Real.sqrt |target - source| * |target - source|) := numerator_bound
    _ = ((2 * speed * holder / chord ^ 2) / Real.sqrt |target - source|) *
        (chord * |target - source|) ^ 2 := by
      have algebra : ∀ distance : ℝ, 0 < distance →
          2 * speed * (holder * Real.sqrt distance * distance) =
            ((2 * speed * holder / chord ^ 2) / Real.sqrt distance) * (chord * distance) ^ 2 := by
        intro distance positive
        field_simp
        calc
          _ = 2 * speed * holder * chord ^ 2 * distance * (Real.sqrt distance ^ 2) := by ring
          _ = _ := by rw [Real.sq_sqrt positive.le]; ring
      exact algebra _ distance_pos
    _ ≤ _ := mul_le_mul_of_nonneg_left (sq_le_sq₀ (by positivity) (norm_nonneg _) |>.mpr chord_bound)
      (by positivity)

theorem real_div_smul_eq_phase {position tangent : ℂ} (separated : position ≠ 0) :
    (tangent / position).re • position =
      (tangent + (position / star position) * star tangent) / 2 := by
  rw [Complex.real_smul, Complex.re_eq_add_conj]
  simp only [map_div, Complex.star_def]
  have conjugate_ne : starRingEnd ℂ position ≠ 0 := by simpa using separated
  field_simp
  ring

theorem continuous_log_norm_smul : Continuous (fun position : ℂ => Real.log ‖position‖ • position) := by
  apply continuous_iff_continuousAt.mpr
  intro position
  by_cases zero : position = 0
  · subst position
    simp only [ContinuousAt, norm_zero, Real.log_zero, zero_smul]
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have limit := ((Real.continuous_mul_log.comp continuous_norm).abs).tendsto (0 : ℂ)
    simpa only [Function.comp_apply, norm_smul, Real.norm_eq_abs, abs_mul, abs_norm, mul_comm, norm_zero,
      Real.log_zero, zero_mul, abs_zero] using limit
  · exact (continuous_norm.continuousAt.log (norm_ne_zero_iff.mpr zero)).smul continuousAt_id

theorem contour_log_product_source_derivative {curve tangent : ℝ → ℂ}
    {target source : ℝ} (derivative : HasDerivAt curve (tangent source) source)
    (separated : curve source - curve target ≠ 0) :
    HasDerivAt (fun x => Real.log ‖curve x - curve target‖ • (curve x - curve target))
      (Real.log ‖curve source - curve target‖ • tangent source +
        (tangent source + contourChordPhase curve source target * star (tangent source)) / 2) source := by
  have log_derivative := contour_log_kernel_derivative_cauchy derivative separated
  have product_derivative := log_derivative.smul (derivative.sub_const (curve target))
  convert product_derivative using 1
  rw [real_div_smul_eq_phase separated]
  rfl

theorem contourChordPhase_integrand_integrable_right {curve tangent : ℝ → ℂ}
    {radius speed : ℝ} (radius_pos : 0 < radius)
    (curve_continuous : ContinuousOn curve (Icc 0 radius))
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (separated : ∀ x ∈ Ioc 0 radius, curve x - curve 0 ≠ 0) :
    IntervalIntegrable (fun x => contourChordPhase curve x 0 * star (tangent x)) volume 0 radius := by
  have difference_continuous : ContinuousOn (fun x : ℝ => curve x - curve 0) (Ioo 0 radius) :=
    (curve_continuous.mono Ioo_subset_Icc_self).sub continuousOn_const
  have denominator_continuous : ContinuousOn (fun x : ℝ => star (curve x - curve 0))
      (Ioo 0 radius) := difference_continuous.star
  have denominator_nonzero : ∀ x ∈ Ioo 0 radius, star (curve x - curve 0) ≠ 0 := by
    intro x hx
    exact star_ne_zero.mpr (separated x ⟨hx.1, hx.2.le⟩)
  have phase_continuous : ContinuousOn (fun x : ℝ => contourChordPhase curve x 0) (Ioo 0 radius) :=
    difference_continuous.div denominator_continuous denominator_nonzero
  have weighted_continuous : ContinuousOn
      (fun x : ℝ => contourChordPhase curve x 0 * star (tangent x)) (Ioo 0 radius) :=
    phase_continuous.mul (tangent_continuous.mono Ioo_subset_Icc_self).star
  have finite : volume (Ioo (0 : ℝ) radius) < ⊤ := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le radius_pos.le]
  have measurable : AEStronglyMeasurable
      (fun x : ℝ => contourChordPhase curve x 0 * star (tangent x))
      (volume.restrict (Ioo 0 radius)) :=
    weighted_continuous.aestronglyMeasurable (μ := volume) measurableSet_Ioo
  have majorant : IntegrableOn (fun _ : ℝ => speed) (Ioo 0 radius) volume :=
    integrableOn_const.2 (Or.inr finite)
  have bound : ∀ᵐ x ∂volume.restrict (Ioo 0 radius),
      ‖contourChordPhase curve x 0 * star (tangent x)‖ ≤ speed := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx
    have phase_norm : ‖contourChordPhase curve x 0‖ = 1 :=
      contourChordPhase_norm (separated x ⟨hx.1, hx.2.le⟩)
    rw [norm_mul, norm_star, phase_norm, one_mul]
    exact tangent_bound x ⟨hx.1.le, hx.2.le⟩
  exact majorant.mono' measurable bound

theorem contour_log_integration_by_parts_right {curve tangent : ℝ → ℂ}
    {radius chord speed : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (derivative : ∀ x ∈ Icc 0 radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc 0 radius))
    (tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Ioc 0 radius, chord * x ≤ ‖curve x - curve 0‖) :
    (∫ x in (0 : ℝ)..radius, Real.log ‖curve x - curve 0‖ • tangent x) =
      Real.log ‖curve radius - curve 0‖ • (curve radius - curve 0) -
        ((curve radius - curve 0) +
          ∫ x in (0 : ℝ)..radius, contourChordPhase curve x 0 * star (tangent x)) / 2 := by
  have curve_continuous : ContinuousOn curve (Icc 0 radius) :=
    fun x hx => (derivative x hx).continuousAt.continuousWithinAt
  have separated : ∀ x ∈ Ioc 0 radius, curve x - curve 0 ≠ 0 := by
    intro x hx
    exact norm_ne_zero_iff.mp (ne_of_gt ((mul_pos chord_pos hx.1).trans_le (chord_bound x hx)))
  have tangent_integrable : IntervalIntegrable tangent volume 0 radius :=
    tangent_continuous.intervalIntegrable_of_Icc radius_pos.le
  have phase_integrable := contourChordPhase_integrand_integrable_right radius_pos curve_continuous
    tangent_continuous tangent_bound separated
  have log_integrable : IntervalIntegrable
      (fun x => Real.log ‖curve x - curve 0‖ • tangent x) volume 0 radius := by
    simpa only [norm_sub_rev] using contourVelocity_integrable_right radius_pos chord_pos speed_pos
      curve_continuous tangent_continuous
      (fun x hx => by simpa only [norm_sub_rev] using chord_bound x hx)
      (fun x hx => contour_speed_bound derivative tangent_bound x ⟨hx.1.le, hx.2⟩) tangent_bound
  have rest_integrable := (tangent_integrable.add phase_integrable).div_const (2 : ℂ)
  have total_integrable := log_integrable.add rest_integrable
  have boundary := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le radius_pos.le
    (continuous_log_norm_smul.comp_continuousOn (curve_continuous.sub continuousOn_const))
    (fun x hx => contour_log_product_source_derivative (derivative x ⟨hx.1.le, hx.2.le⟩)
      (separated x ⟨hx.1, hx.2.le⟩)) total_integrable
  rw [intervalIntegral.integral_add log_integrable rest_integrable,
    intervalIntegral.integral_div,
    intervalIntegral.integral_add tangent_integrable phase_integrable] at boundary
  have tangent_integral := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => derivative x (by simpa only [uIcc_of_le radius_pos.le] using hx)) tangent_integrable
  rw [tangent_integral] at boundary
  simpa only [Function.comp_apply, sub_self, norm_zero, Real.log_zero, zero_smul, sub_zero] using
    (eq_sub_iff_add_eq.mpr boundary)

theorem contour_log_integration_by_parts_closed_split {curve tangent : ℝ → ℂ}
    {radius chord speed : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖)
    (closed : curve (-radius) = curve radius) :
    (∫ x in (-radius)..0, Real.log ‖curve x - curve 0‖ • tangent x) +
      (∫ x in (0 : ℝ)..radius, Real.log ‖curve x - curve 0‖ • tangent x) =
      -((∫ x in (-radius)..0, contourChordPhase curve x 0 * star (tangent x)) +
        (∫ x in (0 : ℝ)..radius, contourChordPhase curve x 0 * star (tangent x))) / 2 := by
  have right_mem : ∀ x ∈ Icc 0 radius, x ∈ Icc (-radius) radius := by
    intro x hx
    exact ⟨(neg_nonpos.mpr radius_pos.le).trans hx.1, hx.2⟩
  have left_mem : ∀ x ∈ Icc 0 radius, -x ∈ Icc (-radius) radius := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have right_identity := contour_log_integration_by_parts_right radius_pos chord_pos speed_pos
    (fun x hx => derivative x (right_mem x hx))
    (tangent_continuous.mono (by intro x hx; exact right_mem x hx))
    (fun x hx => tangent_bound x (right_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))
  have left_identity := contour_log_integration_by_parts_right
    (curve := fun x => curve (-x)) (tangent := fun x => -tangent (-x))
    radius_pos chord_pos speed_pos
    (fun x hx => by
      convert (derivative (-x) (left_mem x hx)).scomp x (hasDerivAt_id x).neg using 1
      simp)
    ((tangent_continuous.comp continuousOn_neg (fun x hx => left_mem x hx)).neg)
    (fun x hx => by simpa using tangent_bound (-x) (left_mem x hx))
    (fun x hx => by simpa [abs_of_pos hx.1] using
      (chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
  simp only [neg_zero, smul_neg, star_neg, mul_neg, intervalIntegral.integral_neg,
    contourChordPhase] at left_identity
  rw [intervalIntegral.integral_comp_neg
    (fun x => Real.log ‖curve x - curve 0‖ • tangent x)] at left_identity
  rw [intervalIntegral.integral_comp_neg
    (fun x => (curve x - curve 0) / star (curve x - curve 0) * star (tangent x))] at left_identity
  have phase_integral_eq :
      (∫ x in (-radius)..(-0), (curve x - curve 0) / star (curve x - curve 0) * star (tangent x)) =
        ∫ x in (-radius)..(-0), contourChordPhase curve x 0 * star (tangent x) := rfl
  rw [phase_integral_eq] at left_identity
  simp only [neg_zero, closed] at left_identity
  rw [right_identity]
  have left_rearranged := congrArg Neg.neg left_identity
  simp only [neg_neg] at left_rearranged
  rw [left_rearranged]
  ring

theorem contour_log_and_phase_integrable {curve tangent : ℝ → ℂ}
    {radius chord speed : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖) :
    IntervalIntegrable (fun x => Real.log ‖curve x - curve 0‖ • tangent x) volume (-radius) radius ∧
      IntervalIntegrable (fun x => contourChordPhase curve x 0 * star (tangent x))
        volume (-radius) radius := by
  have right_mem : ∀ x ∈ Icc 0 radius, x ∈ Icc (-radius) radius := by
    intro x hx
    exact ⟨(neg_nonpos.mpr radius_pos.le).trans hx.1, hx.2⟩
  have left_mem : ∀ x ∈ Icc 0 radius, -x ∈ Icc (-radius) radius := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  have right_derivative : ∀ x ∈ Icc 0 radius, HasDerivAt curve (tangent x) x :=
    fun x hx => derivative x (right_mem x hx)
  have reflected_derivative : ∀ x ∈ Icc 0 radius,
      HasDerivAt (fun y => curve (-y)) (-tangent (-x)) x := by
    intro x hx
    convert (derivative (-x) (left_mem x hx)).scomp x (hasDerivAt_id x).neg using 1
    simp
  have right_continuous : ContinuousOn curve (Icc 0 radius) :=
    fun x hx => (right_derivative x hx).continuousAt.continuousWithinAt
  have reflected_continuous : ContinuousOn (fun y => curve (-y)) (Icc 0 radius) :=
    fun x hx => (reflected_derivative x hx).continuousAt.continuousWithinAt
  have right_tangent_continuous := tangent_continuous.mono (by intro x hx; exact right_mem x hx)
  have reflected_tangent_continuous :=
    (tangent_continuous.comp continuousOn_neg (fun x hx => left_mem x hx)).neg
  have right_tangent_bound : ∀ x ∈ Icc 0 radius, ‖tangent x‖ ≤ speed :=
    fun x hx => tangent_bound x (right_mem x hx)
  have reflected_tangent_bound : ∀ x ∈ Icc 0 radius, ‖-tangent (-x)‖ ≤ speed := by
    intro x hx
    simpa using tangent_bound (-x) (left_mem x hx)
  have right_log : IntervalIntegrable (fun x => Real.log ‖curve x - curve 0‖ • tangent x)
      volume 0 radius := by
    simpa only [norm_sub_rev] using contourVelocity_integrable_right radius_pos chord_pos speed_pos
      right_continuous right_tangent_continuous
      (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
        (chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))
      (fun x hx => contour_speed_bound right_derivative right_tangent_bound x ⟨hx.1.le, hx.2⟩)
      right_tangent_bound
  have reflected_log := contourVelocity_integrable_right radius_pos chord_pos speed_pos
    reflected_continuous reflected_tangent_continuous
    (fun x hx => by simpa [abs_of_pos hx.1, norm_sub_rev] using
      (chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))
    (fun x hx => contour_speed_bound reflected_derivative reflected_tangent_bound x ⟨hx.1.le, hx.2⟩)
    reflected_tangent_bound
  have left_log : IntervalIntegrable (fun x => Real.log ‖curve x - curve 0‖ • tangent x)
      volume (-radius) 0 := by
    have reflected_twice := (IntervalIntegrable.iff_comp_neg.mp reflected_log.neg).symm
    simpa only [Pi.neg_apply, Function.comp_apply, neg_zero, neg_neg, smul_neg, norm_sub_rev]
      using reflected_twice
  have right_phase := contourChordPhase_integrand_integrable_right radius_pos right_continuous
    right_tangent_continuous right_tangent_bound (fun x hx => norm_ne_zero_iff.mp
      (ne_of_gt ((mul_pos chord_pos hx.1).trans_le
        (by simpa [abs_of_pos hx.1] using chord_bound x (right_mem x ⟨hx.1.le, hx.2⟩)))))
  have reflected_phase := contourChordPhase_integrand_integrable_right radius_pos reflected_continuous
    reflected_tangent_continuous reflected_tangent_bound (fun x hx => norm_ne_zero_iff.mp
      (ne_of_gt ((mul_pos chord_pos hx.1).trans_le
        (by simpa [abs_of_pos hx.1] using chord_bound (-x) (left_mem x ⟨hx.1.le, hx.2⟩)))))
  have left_phase : IntervalIntegrable (fun x => contourChordPhase curve x 0 * star (tangent x))
      volume (-radius) 0 := by
    have reflected_twice := (IntervalIntegrable.iff_comp_neg.mp reflected_phase.neg).symm
    simpa only [Pi.neg_apply, Function.comp_apply, contourChordPhase, neg_zero, neg_neg, star_neg, mul_neg]
      using reflected_twice
  exact ⟨left_log.trans right_log, left_phase.trans right_phase⟩

theorem contourVelocity_eq_phase_integral {curve tangent : ℝ → ℂ}
    {radius chord speed : ℝ} (radius_pos : 0 < radius)
    (chord_pos : 0 < chord) (speed_pos : 0 < speed)
    (derivative : ∀ x ∈ Icc (-radius) radius, HasDerivAt curve (tangent x) x)
    (tangent_continuous : ContinuousOn tangent (Icc (-radius) radius))
    (tangent_bound : ∀ x ∈ Icc (-radius) radius, ‖tangent x‖ ≤ speed)
    (chord_bound : ∀ x ∈ Icc (-radius) radius, chord * |x| ≤ ‖curve x - curve 0‖)
    (closed : curve (-radius) = curve radius) :
    contourVelocity curve tangent 0 (-radius) radius =
      (1 / (4 * Real.pi)) •
        ∫ x in (-radius)..radius, contourChordPhase curve x 0 * star (tangent x) := by
  obtain ⟨log_integrable, phase_integrable⟩ := contour_log_and_phase_integrable
    radius_pos chord_pos speed_pos derivative tangent_continuous tangent_bound chord_bound
  have zero_mem : (0 : ℝ) ∈ uIcc (-radius) radius := by
    rw [uIcc_of_le (by linarith)]
    constructor <;> linarith
  have identity := contour_log_integration_by_parts_closed_split radius_pos chord_pos speed_pos
    derivative tangent_continuous tangent_bound chord_bound closed
  rw [intervalIntegral.integral_add_adjacent_intervals
    (log_integrable.mono_set (uIcc_subset_uIcc_left zero_mem))
    (log_integrable.mono_set (uIcc_subset_uIcc_right zero_mem)),
    intervalIntegral.integral_add_adjacent_intervals
    (phase_integrable.mono_set (uIcc_subset_uIcc_left zero_mem))
    (phase_integrable.mono_set (uIcc_subset_uIcc_right zero_mem))] at identity
  unfold contourVelocity
  simp only [norm_sub_rev]
  rw [identity, Complex.real_smul, Complex.real_smul]
  push_cast
  ring

theorem contourVelocity_rigid_motion (curve tangent : ℝ → ℂ) (target lower upper : ℝ)
    (rotation center : ℂ) (unit_rotation : ‖rotation‖ = 1) :
    contourVelocity (fun x => rotation * curve x + center) (fun x => rotation * tangent x)
      target lower upper = rotation * contourVelocity curve tangent target lower upper := by
  unfold contourVelocity
  have integrand_identity :
      (fun source => Real.log ‖rotation * curve target + center - (rotation * curve source + center)‖ •
        (rotation * tangent source)) =
      fun source => rotation * (Real.log ‖curve target - curve source‖ • tangent source) := by
    funext source
    rw [add_sub_add_right_eq_sub, ← mul_sub, norm_mul, unit_rotation, one_mul]
    simp only [Complex.real_smul]
    ring
  rw [integrand_identity, intervalIntegral.integral_const_mul]
  simp only [Complex.real_smul]
  ring

theorem contourVelocity_shift_parameter (curve tangent : ℝ → ℂ)
    (target lower upper offset : ℝ) :
    contourVelocity (fun x => curve (x + offset)) (fun x => tangent (x + offset)) target lower upper =
      contourVelocity curve tangent (target + offset) (lower + offset) (upper + offset) := by
  unfold contourVelocity
  rw [intervalIntegral.integral_comp_add_right
    (fun source => Real.log ‖curve (target + offset) - curve source‖ • tangent source)]

end EulerNonuniqueness.Paper
