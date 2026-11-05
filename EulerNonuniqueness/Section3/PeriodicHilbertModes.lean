import EulerNonuniqueness.Section3.PeriodicHilbertComplex

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

local instance : NormedSpace ℝ PeriodicHolderHalf := Submodule.normedSpace periodicHolderGraph
local instance : NormedSpace ℝ PeriodicC1HolderHalf := Submodule.normedSpace periodicC1HolderGraph
local instance : NormedSpace ℂ PeriodicHolderHalf := complexHolderNormedSpace

def positiveCircleMode : ℕ → PeriodicHolderHalf
  | 0 => c1ValueHolder (c1Constant 1)
  | degree + 1 => holderProduct (c1ValueHolder standardCircleBanach) (positiveCircleMode degree)

theorem positiveCircleMode_value (degree : ℕ) (label : ℝ) :
    (positiveCircleMode degree).val.1 label = standardCircle label ^ degree := by
  induction degree with
  | zero => rfl
  | succ degree induction =>
    change standardCircle label * (positiveCircleMode degree).val.1 label = _
    rw [induction, pow_succ]
    ring

theorem standardCircle_pow_hasDerivAt (degree : ℕ) (label : ℝ) :
    HasDerivAt (fun current => standardCircle current ^ (degree + 1))
      (((degree + 1 : ℕ) : ℂ) * Complex.I * standardCircle label ^ (degree + 1)) label := by
  convert (hasDerivAt_pow (degree + 1) (standardCircle label)).comp label
    (standardCircle_derivative label) using 1
  simp only [Nat.add_sub_cancel, standardCircleTangent, pow_succ]
  ring

theorem integral_standardCircle_pow_succ (degree : ℕ) :
    (∫ source in (-Real.pi)..Real.pi, standardCircle source ^ (degree + 1)) = 0 := by
  have coefficientNonzero : (((degree + 1 : ℕ) : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero degree) Complex.I_ne_zero
  have derivative (source : ℝ) :
      HasDerivAt (fun current => standardCircle current ^ (degree + 1) /
        (((degree + 1 : ℕ) : ℂ) * Complex.I))
        (standardCircle source ^ (degree + 1)) source := by
    convert (standardCircle_pow_hasDerivAt degree source).div_const
      (((degree + 1 : ℕ) : ℂ) * Complex.I) using 1
    exact (mul_div_cancel_left₀ _ coefficientNonzero).symm
  have continuousCircle : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr (fun source => (standardCircle_derivative source).continuousAt)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun source _ => derivative source)
    ((continuousCircle.pow _).intervalIntegrable _ _)]
  have endpoints : standardCircle Real.pi = standardCircle (-Real.pi) := by
    simp [standardCircle, Complex.exp_neg]
  rw [endpoints, sub_self]

theorem circleCauchyTranslatedRemainder_mode_succ (degree : ℕ) {source : ℝ}
    (inside : source ∈ Icc (-Real.pi) Real.pi) (nonzero : source ≠ 0) :
    circleCauchyTranslatedRemainder (positiveCircleMode (degree + 1)).val.1 0 source =
      circleCauchyTranslatedRemainder (positiveCircleMode degree).val.1 0 source -
        Complex.I * standardCircle source ^ (degree + 1) := by
  have lower := standardCircle_chord_bound source inside
  have positive : 0 < ‖standardCircle source - standardCircle 0‖ :=
    (mul_pos (by positivity : 0 < 2 / Real.pi) (abs_pos.mpr nonzero)).trans_le lower
  have separated : standardCircle 0 - standardCircle source ≠ 0 := by
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (norm_ne_zero_iff.mp positive.ne')))
  unfold circleCauchyTranslatedRemainder
  simp only [positiveCircleMode_value, add_zero]
  have circleZero : standardCircle 0 = 1 := by simp [standardCircle]
  rw [circleZero] at separated
  simp only [circleZero, one_pow]
  unfold standardCircleTangent
  field_simp [separated]
  ring

theorem integral_circleCauchyTranslatedRemainder_mode (degree : ℕ) :
    (∫ source in (-Real.pi)..Real.pi,
      circleCauchyTranslatedRemainder (positiveCircleMode degree).val.1 0 source) = 0 := by
  induction degree with
  | zero =>
    have integrand : circleCauchyTranslatedRemainder (positiveCircleMode 0).val.1 0 = 0 := by
      funext source
      simp [circleCauchyTranslatedRemainder, positiveCircleMode_value]
    rw [integrand]
    simp only [Pi.zero_apply, intervalIntegral.integral_zero]
  | succ degree induction =>
    have identity :
        (∫ source in (-Real.pi)..Real.pi,
          circleCauchyTranslatedRemainder (positiveCircleMode (degree + 1)).val.1 0 source) =
        ∫ source in (-Real.pi)..Real.pi,
          circleCauchyTranslatedRemainder (positiveCircleMode degree).val.1 0 source -
            Complex.I * standardCircle source ^ (degree + 1) := by
      apply intervalIntegral.integral_congr_ae
      have almostNonzero : ∀ᵐ source : ℝ ∂volume, source ≠ 0 := by simp [ae_iff]
      filter_upwards [almostNonzero] with source nonzero
      intro inside
      rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at inside
      exact circleCauchyTranslatedRemainder_mode_succ degree ⟨inside.1.le, inside.2⟩ nonzero
    have continuousCircle : Continuous standardCircle :=
      continuous_iff_continuousAt.mpr (fun source => (standardCircle_derivative source).continuousAt)
    rw [identity, intervalIntegral.integral_sub
      (circleCauchyTranslatedRemainder_integrable (positiveCircleMode degree) 0)
      (((continuousCircle.pow _).intervalIntegrable _ _).const_mul Complex.I),
      intervalIntegral.integral_const_mul, integral_standardCircle_pow_succ, induction, mul_zero, sub_zero]

theorem circleCauchyCLM_mode_zero (degree : ℕ) :
    (circleCauchyCLM (positiveCircleMode degree)).val.1 0 = -(Real.pi : ℂ) * Complex.I := by
  rw [circleCauchyCLM_translated, integral_circleCauchyTranslatedRemainder_mode,
    positiveCircleMode_value]
  simp [standardCircle]

theorem positiveCircleMode_shift (degree : ℕ) (offset : ℝ) :
    holderLabelShift offset (positiveCircleMode degree) =
      standardCircle offset ^ degree • positiveCircleMode degree := by
  apply PeriodicHolderHalf.ext_value
  intro source
  simp only [holderLabelShift_value, positiveCircleMode_value, complexHolder_smul_value,
    standardCircle_add, mul_pow]
  ring

theorem circleCauchyCLM_mode (degree : ℕ) :
    circleCauchyCLM (positiveCircleMode degree) =
      (-(Real.pi : ℂ) * Complex.I) • positiveCircleMode degree := by
  apply PeriodicHolderHalf.ext_value
  intro target
  have identity := congrArg (fun density : PeriodicHolderHalf => density.val.1 0)
    (circleCauchyCLM_shift target (positiveCircleMode degree))
  rw [positiveCircleMode_shift, circleCauchyCLM_smul_complex] at identity
  dsimp only at identity
  rw [complexHolder_smul_value, circleCauchyCLM_mode_zero, holderLabelShift_value, zero_add] at identity
  change (circleCauchyCLM (positiveCircleMode degree)).val.1 target =
    (-(Real.pi : ℂ) * Complex.I) * (positiveCircleMode degree).val.1 target
  rw [← identity, positiveCircleMode_value]
  ring

theorem circleCauchyKernel_sub_star {source : ℝ}
    (inside : source ∈ Icc (-Real.pi) Real.pi) (nonzero : source ≠ 0) :
    standardCircleTangent source / (standardCircle 0 - standardCircle source) -
      star (standardCircleTangent source / (standardCircle 0 - standardCircle source)) = -Complex.I := by
  have lower := standardCircle_chord_bound source inside
  have positive : 0 < ‖standardCircle source - standardCircle 0‖ :=
    (mul_pos (by positivity : 0 < 2 / Real.pi) (abs_pos.mpr nonzero)).trans_le lower
  have circleZero : standardCircle 0 = 1 := by simp [standardCircle]
  have separated : 1 - standardCircle source ≠ 0 := by
    rw [← circleZero]
    exact sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp (norm_ne_zero_iff.mp positive.ne')))
  have starSeparated : 1 - star (standardCircle source) ≠ 0 := by
    simpa only [star_sub, star_one] using star_ne_zero.mpr separated
  have unit : standardCircle source * star (standardCircle source) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, standardCircle_norm]
    norm_num
  rw [circleZero]
  unfold standardCircleTangent
  simp only [Complex.star_def, map_div, map_mul, Complex.conj_I, map_sub, map_one] at starSeparated unit ⊢
  field_simp [separated, starSeparated]
  linear_combination -Complex.I * unit

theorem circleCauchyTranslatedRemainder_conjugate (density : PeriodicHolderHalf)
    {source : ℝ} (inside : source ∈ Icc (-Real.pi) Real.pi) (nonzero : source ≠ 0) :
    circleCauchyTranslatedRemainder (holderConjugate density).val.1 0 source =
      star (circleCauchyTranslatedRemainder density.val.1 0 source) -
        Complex.I * (star (density.val.1 source) - star (density.val.1 0)) := by
  have kernel := circleCauchyKernel_sub_star inside nonzero
  unfold circleCauchyTranslatedRemainder
  simp only [holderConjugate_value, add_zero]
  have conjugateProduct :
      star ((density.val.1 source - density.val.1 0) * standardCircleTangent source /
        (standardCircle 0 - standardCircle source)) =
      (star (density.val.1 source) - star (density.val.1 0)) *
        star (standardCircleTangent source / (standardCircle 0 - standardCircle source)) := by
    simp only [Complex.star_def, map_div₀, map_mul, map_sub]
    ring
  rw [conjugateProduct, mul_div_assoc]
  linear_combination (star (density.val.1 source) - star (density.val.1 0)) * kernel

theorem circleCauchyCLM_conjugate_zero (density : PeriodicHolderHalf) :
    (circleCauchyCLM (holderConjugate density)).val.1 0 =
      star ((circleCauchyCLM density).val.1 0) -
        Complex.I * ∫ source in (-Real.pi)..Real.pi, star (density.val.1 source) := by
  let conjugation : ℂ →L[ℝ] ℂ := Complex.conjCLE
  have integrable := circleCauchyTranslatedRemainder_integrable density 0
  have conjugateIntegrable : IntervalIntegrable
      (fun source => star (circleCauchyTranslatedRemainder density.val.1 0 source))
      volume (-Real.pi) Real.pi :=
    ⟨conjugation.integrable_comp integrable.1, conjugation.integrable_comp integrable.2⟩
  have densityIntegrable := (continuous_star.comp density.val.1.continuous).intervalIntegrable (μ := volume)
    (-Real.pi) Real.pi
  change IntervalIntegrable (fun source => star (density.val.1 source)) volume
    (-Real.pi) Real.pi at densityIntegrable
  have constantIntegrable : IntervalIntegrable (fun _ : ℝ => star (density.val.1 0))
      volume (-Real.pi) Real.pi := intervalIntegrable_const
  have identity :
      (∫ source in (-Real.pi)..Real.pi,
        circleCauchyTranslatedRemainder (holderConjugate density).val.1 0 source) =
      ∫ source in (-Real.pi)..Real.pi,
        star (circleCauchyTranslatedRemainder density.val.1 0 source) -
          Complex.I * (star (density.val.1 source) - star (density.val.1 0)) := by
    apply intervalIntegral.integral_congr_ae
    have almostNonzero : ∀ᵐ source : ℝ ∂volume, source ≠ 0 := by simp [ae_iff]
    filter_upwards [almostNonzero] with source nonzero
    intro inside
    rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at inside
    exact circleCauchyTranslatedRemainder_conjugate density ⟨inside.1.le, inside.2⟩ nonzero
  have conjugateIntegral :
      (∫ source in (-Real.pi)..Real.pi,
        star (circleCauchyTranslatedRemainder density.val.1 0 source)) =
      star (∫ source in (-Real.pi)..Real.pi,
        circleCauchyTranslatedRemainder density.val.1 0 source) :=
    conjugation.intervalIntegral_comp_comm integrable
  rw [circleCauchyCLM_translated, circleCauchyCLM_translated, identity,
    intervalIntegral.integral_sub conjugateIntegrable
      ((densityIntegrable.sub constantIntegrable).const_mul Complex.I),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub densityIntegrable constantIntegrable,
    intervalIntegral.integral_const, conjugateIntegral, holderConjugate_value]
  simp only [Complex.star_def, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_neg]
  ring

theorem periodicHilbertCLM_mode_zero (degree : ℕ) :
    (periodicHilbertCLM (positiveCircleMode (degree + 1))).val.1 0 = -Complex.I := by
  have continuousCircle : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr (fun source => (standardCircle_derivative source).continuousAt)
  have conjugateIntegral :
      (∫ source in (-Real.pi)..Real.pi, star (standardCircle source ^ (degree + 1))) = 0 := by
    have identity := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm
      ((continuousCircle.pow (degree + 1)).intervalIntegrable (μ := volume) (-Real.pi) Real.pi)
    change (∫ source in (-Real.pi)..Real.pi, star (standardCircle source ^ (degree + 1))) =
      star (∫ source in (-Real.pi)..Real.pi, standardCircle source ^ (degree + 1)) at identity
    rw [integral_standardCircle_pow_succ, star_zero] at identity
    exact identity
  change (1 / (2 * Real.pi)) •
    ((circleCauchyCLM (positiveCircleMode (degree + 1))).val.1 0 +
      star ((circleCauchyCLM (holderConjugate (positiveCircleMode (degree + 1)))).val.1 0)) = _
  rw [circleCauchyCLM_conjugate_zero, circleCauchyCLM_mode_zero]
  simp_rw [positiveCircleMode_value]
  rw [conjugateIntegral]
  simp only [mul_zero, sub_zero, star_star, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have piNonzero : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [piNonzero]
  ring

theorem periodicHilbertCLM_positive_mode (degree : ℕ) :
    periodicHilbertCLM (positiveCircleMode (degree + 1)) =
      (-Complex.I) • positiveCircleMode (degree + 1) := by
  apply PeriodicHolderHalf.ext_value
  intro target
  have identity := congrArg (fun density : PeriodicHolderHalf => density.val.1 0)
    (periodicHilbertCLM_shift target (positiveCircleMode (degree + 1)))
  rw [positiveCircleMode_shift, periodicHilbertCLM_smul_complex] at identity
  dsimp only at identity
  rw [complexHolder_smul_value, periodicHilbertCLM_mode_zero, holderLabelShift_value, zero_add] at identity
  change (periodicHilbertCLM (positiveCircleMode (degree + 1))).val.1 target =
    -Complex.I * (positiveCircleMode (degree + 1)).val.1 target
  rw [← identity, positiveCircleMode_value]
  ring

theorem periodicHilbertCLM_negative_mode (degree : ℕ) :
    periodicHilbertCLM (holderConjugate (positiveCircleMode (degree + 1))) =
      Complex.I • holderConjugate (positiveCircleMode (degree + 1)) := by
  rw [periodicHilbertCLM_conjugate, periodicHilbertCLM_positive_mode, holderConjugate_smul_complex]
  congr 1
  simp [Complex.star_def]

theorem periodicHilbertCLM_constant_mode : periodicHilbertCLM (positiveCircleMode 0) = 0 := by
  have real : holderConjugate (positiveCircleMode 0) = positiveCircleMode 0 := by
    apply PeriodicHolderHalf.ext_value
    intro label
    simp only [holderConjugate_value, positiveCircleMode_value, pow_zero, star_one]
  apply PeriodicHolderHalf.ext_value
  intro target
  change (1 / (2 * Real.pi)) •
    ((circleCauchyCLM (positiveCircleMode 0)).val.1 target +
      star ((circleCauchyCLM (holderConjugate (positiveCircleMode 0))).val.1 target)) = 0
  rw [real, circleCauchyCLM_mode]
  simp [complexHolder_smul_value, positiveCircleMode_value, Complex.star_def]

end

end EulerNonuniqueness.Paper
