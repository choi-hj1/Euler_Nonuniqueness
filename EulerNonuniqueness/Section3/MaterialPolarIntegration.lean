import EulerNonuniqueness.Section3.PolarIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

def radialTestIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (function : ℂ → E) (angle : ℝ) : E :=
  ∫ radius in (0 : ℝ)..profile angle, radius • function ((radius : ℂ) * standardCircle angle)

theorem radialTestIntegral_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (function : ℂ → E) (profile_continuous : Continuous profile)
    (function_continuous : Continuous function) : Continuous (radialTestIntegral profile function) := by
  have circle_continuous : Continuous standardCircle := standardCircleBanach.val.1.continuous
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (μ := volume) _ profile_continuous
  exact continuous_snd.smul (function_continuous.comp
    ((Complex.continuous_ofReal.comp continuous_snd).mul (circle_continuous.comp continuous_fst)))

theorem radialTestIntegral_periodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (profile : ℝ → ℝ) (function : ℂ → E) (periodic : Function.Periodic profile (2 * Real.pi)) :
    Function.Periodic (radialTestIntegral profile function) (2 * Real.pi) := by
  intro angle
  unfold radialTestIntegral
  rw [periodic angle]
  apply intervalIntegral.integral_congr
  intro radius radius_mem
  dsimp only
  rw [standardCircle_periodic angle]

theorem nearCircle_angular_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1)
    (function : ℝ → E) (function_continuous : Continuous function)
    (periodic : Function.Periodic function (2 * Real.pi)) :
    (∫ label in (-Real.pi)..Real.pi,
      (data.val.2.val.1 label / data.val.1 label).im • function (nearCircleAngularLift data label)) =
      ∫ angle in (-Real.pi)..Real.pi, function angle := by
  have nonzero : ∀ label, data.val.1 label ≠ 0 := by
    intro label
    apply norm_pos_iff.mp
    have lower := nearCircle_value_lower_bound data label
    linarith
  have derivative_continuous : Continuous (fun label => (data.val.2.val.1 label / data.val.1 label).im) :=
    Complex.continuous_im.comp (data.val.2.val.1.continuous.div data.val.1.continuous nonzero)
  have substitution := intervalIntegral.integral_comp_smul_deriv
    (a := -Real.pi) (b := Real.pi)
    (fun label _ => nearCircleAngularLift_hasDerivAt data small label)
    derivative_continuous.continuousOn function_continuous
  have endpoint : nearCircleAngularLift data Real.pi = nearCircleAngularLift data (-Real.pi) + 2 * Real.pi := by
    convert nearCircleAngularLift_add_period data (-Real.pi) using 1
    congr 1
    ring
  rw [endpoint, periodic.intervalIntegral_add_eq (nearCircleAngularLift data (-Real.pi)) (-Real.pi)] at substitution
  simpa only [Function.comp_apply, show -Real.pi + 2 * Real.pi = Real.pi by ring] using substitution

theorem integral_nearCircleInterior_material_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → E) (function_continuous : Continuous function) :
    (∫ position in nearCircleInterior data small, function position) =
      ∫ label in (-Real.pi)..Real.pi, (data.val.2.val.1 label / data.val.1 label).im •
        radialTestIntegral (nearCircleRadialProfile data small) function (nearCircleAngularLift data label) := by
  rw [nearCircleInterior, integral_polarInterior_eq_iterated _ (nearCircleRadialProfile_continuous data small)
    (nearCircleRadialProfile_periodic data small) (by linarith : 0 < 1 - ‖data - standardCircleBanach‖)
    (nearCircleRadialProfile_lower data small) (nearCircleRadialProfile_upper data small) function function_continuous]
  exact (nearCircle_angular_substitution data (small.trans (by norm_num))
    (radialTestIntegral (nearCircleRadialProfile data small) function)
    (radialTestIntegral_continuous _ _ (nearCircleRadialProfile_continuous data small) function_continuous)
    (radialTestIntegral_periodic _ _ (nearCircleRadialProfile_periodic data small))).symm

def radialMaterialPrimitive {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℂ → E) (position : ℂ) : E :=
  ∫ scale in (0 : ℝ)..1, scale • function ((scale : ℂ) * position)

theorem radial_integral_scaling {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (function : ℂ → E) (radius : ℝ) (direction : ℂ) :
    (∫ scale in (0 : ℝ)..radius, scale • function ((scale : ℂ) * direction)) =
      radius^2 • radialMaterialPrimitive function ((radius : ℂ) * direction) := by
  have substitution := intervalIntegral.smul_integral_comp_mul_left
    (fun scale : ℝ => scale • function ((scale : ℂ) * direction)) radius (a := 0) (b := 1)
  rw [mul_zero, mul_one] at substitution
  have integrand_identity :
      (fun scale : ℝ => (radius * scale) • function ((↑(radius * scale) : ℂ) * direction)) =
      (fun scale : ℝ => radius • (scale • function ((scale : ℂ) * ((radius : ℂ) * direction)))) := by
    funext scale
    rw [smul_smul]
    congr 1
    congr 1
    push_cast
    ring
  rw [← substitution, integrand_identity, intervalIntegral.integral_smul, smul_smul, pow_two, radialMaterialPrimitive]

theorem imaginary_div_mul_norm_sq (position tangent : ℂ) (nonzero : position ≠ 0) :
    (tangent / position).im * ‖position‖^2 = (star position * tangent).im := by
  rw [Complex.div_im, Complex.normSq_eq_norm_sq, ← sub_div,
    div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr nonzero))]
  simp only [Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

theorem integral_nearCircleInterior_radial_flux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (data : PeriodicC1HolderHalf) (small : ‖data - standardCircleBanach‖ < 1 / 3)
    (function : ℂ → E) (function_continuous : Continuous function) :
    (∫ position in nearCircleInterior data small, function position) =
      ∫ label in (-Real.pi)..Real.pi,
        (star (data.val.1 label) * data.val.2.val.1 label).im • radialMaterialPrimitive function (data.val.1 label) := by
  rw [integral_nearCircleInterior_material_angle data small function function_continuous]
  apply intervalIntegral.integral_congr
  intro label label_mem
  dsimp only
  have profile_identity : nearCircleRadialProfile data small (nearCircleAngularLift data label) = ‖data.val.1 label‖ := by
    unfold nearCircleRadialProfile
    rw [nearCircleInverseAngle_left]
  rw [radialTestIntegral, profile_identity, radial_integral_scaling,
    ← nearCircle_polar_representation data label, smul_smul]
  congr 1
  apply imaginary_div_mul_norm_sq
  apply norm_pos_iff.mp
  have lower := nearCircle_value_lower_bound data label
  linarith

end

end EulerNonuniqueness.Paper
