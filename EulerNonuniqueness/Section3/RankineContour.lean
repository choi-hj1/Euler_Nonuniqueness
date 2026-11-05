import EulerNonuniqueness.Section3.ContourDynamics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open MeasureTheory Set

namespace EulerNonuniqueness.Paper

noncomputable def standardCircle (parameter : ℝ) : ℂ :=
  Complex.exp ((parameter : ℂ) * Complex.I)

noncomputable def standardCircleTangent (parameter : ℝ) : ℂ :=
  Complex.I * standardCircle parameter

theorem standardCircle_derivative (parameter : ℝ) :
    HasDerivAt standardCircle (standardCircleTangent parameter) parameter := by
  have derivative := ((hasDerivAt_id parameter).ofReal_comp.mul_const Complex.I).cexp
  unfold standardCircleTangent standardCircle
  simpa [mul_comm] using derivative

theorem standardCircle_norm (parameter : ℝ) : ‖standardCircle parameter‖ = 1 := by
  simp [standardCircle, Complex.norm_exp, Complex.mul_re]

theorem standardCircleTangent_norm (parameter : ℝ) : ‖standardCircleTangent parameter‖ = 1 := by
  simp [standardCircleTangent, standardCircle_norm]

theorem standardCircle_norm_sub_one_sq (parameter : ℝ) :
    ‖standardCircle parameter - 1‖ ^ 2 = 2 - 2 * Real.cos parameter := by
  rw [norm_sub_sq_real, standardCircle_norm, Complex.inner]
  simp [standardCircle, Complex.exp_re, Complex.mul_re, Complex.mul_im]
  ring

theorem standardCircle_chord_bound (parameter : ℝ)
    (parameter_mem : parameter ∈ Icc (-Real.pi) Real.pi) :
    (2 / Real.pi) * |parameter| ≤ ‖standardCircle parameter - standardCircle 0‖ := by
  have abs_bound : |parameter| ≤ Real.pi := abs_le.mpr parameter_mem
  have cos_bound := Real.cos_le_one_sub_mul_cos_sq abs_bound
  have square_bound : ((2 / Real.pi) * |parameter|) ^ 2 ≤
      ‖standardCircle parameter - 1‖ ^ 2 := by
    rw [standardCircle_norm_sub_one_sq, mul_pow, div_pow, sq_abs]
    norm_num
    ring_nf at cos_bound ⊢
    linarith
  have : standardCircle 0 = 1 := by simp [standardCircle]
  rw [this]
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp square_bound

theorem unit_circle_phase_integrand {position : ℂ} (unit_norm : ‖position‖ = 1)
    (separated : position ≠ 1) :
    ((position - 1) / star (position - 1)) * star (Complex.I * position) = Complex.I := by
  have square_norm : Complex.normSq position = 1 := by
    rw [Complex.normSq_eq_norm_sq, unit_norm]
    norm_num
  have product : position * star position = 1 := by
    rw [Complex.star_def, Complex.mul_conj, square_norm]
    rfl
  have denominator_ne : star position - 1 ≠ 0 := by
    simpa only [star_sub, star_one] using (star_ne_zero.mpr (sub_ne_zero.mpr separated))
  simp only [star_sub, star_one, star_mul, Complex.star_def, map_sub, map_one,
    Complex.conj_I]
  rw [div_mul_eq_mul_div]
  apply (div_eq_iff denominator_ne).mpr
  calc
    _ = -Complex.I * (position * star position) + Complex.I * star position := by
      simp only [Complex.star_def]
      ring
    _ = _ := by rw [product]; simp [Complex.star_def]; ring

theorem standardCircle_phase_integrand (parameter : ℝ)
    (parameter_mem : parameter ∈ Icc (-Real.pi) Real.pi) (nonzero : parameter ≠ 0) :
    contourChordPhase standardCircle parameter 0 * star (standardCircleTangent parameter) = Complex.I := by
  have separated : standardCircle parameter ≠ 1 := by
    have chord := standardCircle_chord_bound parameter parameter_mem
    have positive : 0 < (2 / Real.pi) * |parameter| := by positivity
    intro equal
    simp only [standardCircle, Complex.ofReal_zero, zero_mul, Complex.exp_zero] at chord
    rw [show Complex.exp ((parameter : ℂ) * Complex.I) = 1 from equal, sub_self, norm_zero] at chord
    exact (not_le_of_gt positive) chord
  simpa [contourChordPhase, standardCircleTangent, standardCircle] using
    unit_circle_phase_integrand (standardCircle_norm parameter) separated

theorem standardCircle_contourVelocity :
    contourVelocity standardCircle standardCircleTangent 0 (-Real.pi) Real.pi = Complex.I / 2 := by
  have circle_continuous : Continuous standardCircle :=
    continuous_iff_continuousAt.mpr (fun parameter => (standardCircle_derivative parameter).continuousAt)
  have tangent_continuous : Continuous standardCircleTangent := by
    change Continuous (fun parameter => Complex.I * standardCircle parameter)
    exact continuous_const.mul circle_continuous
  have closed : standardCircle (-Real.pi) = standardCircle Real.pi := by
    simp [standardCircle, Complex.exp_neg, Complex.exp_pi_mul_I]
  have representation := contourVelocity_eq_phase_integral
    (curve := standardCircle) (tangent := standardCircleTangent) (radius := Real.pi)
    (chord := 2 / Real.pi) (speed := 1) Real.pi_pos (by positivity) (by norm_num)
    (fun parameter _ => standardCircle_derivative parameter) tangent_continuous.continuousOn
    (fun parameter _ => (standardCircleTangent_norm parameter).le)
    (fun parameter membership => standardCircle_chord_bound parameter membership) closed
  have integral_value : (∫ parameter in (-Real.pi)..Real.pi,
      contourChordPhase standardCircle parameter 0 * star (standardCircleTangent parameter)) =
      (2 * Real.pi) • Complex.I := by
    have congruence : (∫ parameter in (-Real.pi)..Real.pi,
        contourChordPhase standardCircle parameter 0 * star (standardCircleTangent parameter)) =
        ∫ _ in (-Real.pi)..Real.pi, Complex.I := by
      apply intervalIntegral.integral_congr_ae
      have nonzero : ∀ᵐ parameter : ℝ ∂volume, parameter ≠ 0 := by
        simp only [ae_iff, not_not, setOf_eq_eq_singleton, measure_singleton]
      filter_upwards [nonzero] with parameter nonzero membership
      rw [uIoc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)] at membership
      exact standardCircle_phase_integrand parameter ⟨membership.1.le, membership.2⟩ nonzero
    rw [congruence, intervalIntegral.integral_const]
    congr 1
    ring
  rw [representation, integral_value, smul_smul, Complex.real_smul]
  push_cast
  have pi_ne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [pi_ne]
  ring

theorem standardCircle_add (first second : ℝ) :
    standardCircle (first + second) = standardCircle first * standardCircle second := by
  simp only [standardCircle, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem standardCircle_contourVelocity_at (parameter : ℝ) :
    contourVelocity standardCircle standardCircleTangent parameter
      (parameter - Real.pi) (parameter + Real.pi) =
      (Complex.I / 2) * standardCircle parameter := by
  have shifted_velocity := contourVelocity_rigid_motion standardCircle standardCircleTangent
    0 (-Real.pi) Real.pi (standardCircle parameter) 0 (standardCircle_norm parameter)
  simp only [add_zero, standardCircle_contourVelocity] at shifted_velocity
  have curve_identity : (fun x => standardCircle parameter * standardCircle x) =
      fun x => standardCircle (x + parameter) := by
    funext x
    rw [standardCircle_add, mul_comm]
  have tangent_identity : (fun x => standardCircle parameter * standardCircleTangent x) =
      fun x => standardCircleTangent (x + parameter) := by
    funext x
    simp only [standardCircleTangent, standardCircle_add]
    ring
  rw [curve_identity, tangent_identity, contourVelocity_shift_parameter] at shifted_velocity
  simpa only [zero_add, add_zero, sub_eq_add_neg, add_comm, mul_comm] using shifted_velocity

theorem standardCircle_rotating_boundary (time label : ℝ) :
    HasDerivAt (fun current => standardCircle (label + current / 2))
      (contourVelocity (fun parameter => standardCircle (parameter + time / 2))
        (fun parameter => standardCircleTangent (parameter + time / 2)) label
        (label - Real.pi) (label + Real.pi)) time := by
  have velocity :
      contourVelocity (fun parameter => standardCircle (parameter + time / 2))
        (fun parameter => standardCircleTangent (parameter + time / 2)) label
        (label - Real.pi) (label + Real.pi) =
      (Complex.I / 2) * standardCircle (label + time / 2) := by
    rw [contourVelocity_shift_parameter]
    convert standardCircle_contourVelocity_at (label + time / 2) using 1 <;> congr 1 <;> ring
  rw [velocity]
  have derivative := (standardCircle_derivative (label + time / 2)).scomp time
    (((hasDerivAt_id time).div_const 2).const_add label)
  convert derivative using 1
  simp only [standardCircleTangent, Complex.real_smul]
  push_cast
  ring

end EulerNonuniqueness.Paper
