import EulerNonuniqueness.Section3.PolarIntegration
import Mathlib.Analysis.SpecialFunctions.Integrals

open Set MeasureTheory

namespace EulerNonuniqueness.Paper

noncomputable section

theorem polarInterior_area (profile : ℝ → ℝ) (profile_continuous : Continuous profile)
    (periodic : Function.Periodic profile (2 * Real.pi)) {lower upper : ℝ} (lower_pos : 0 < lower)
    (profile_lower : ∀ angle, lower ≤ profile angle) (profile_upper : ∀ angle, profile angle ≤ upper) :
    (volume (polarInterior profile)).toReal =
      (∫ angle in (-Real.pi)..Real.pi, (profile angle)^2) / 2 := by
  have identity := integral_polarInterior_eq_iterated profile profile_continuous periodic lower_pos
    profile_lower profile_upper (fun _ : ℂ => (1 : ℝ)) continuous_const
  simpa only [setIntegral_const, smul_eq_mul, mul_one, integral_id, pow_two, zero_mul,
    sub_zero, intervalIntegral.integral_div] using identity

theorem nearCircleInterior_area (data : PeriodicC1HolderHalf)
    (small : ‖data - standardCircleBanach‖ < 1 / 3) :
    (volume (nearCircleInterior data small)).toReal =
      (∫ angle in (-Real.pi)..Real.pi, (nearCircleRadialProfile data small angle)^2) / 2 :=
  polarInterior_area _ (nearCircleRadialProfile_continuous data small) (nearCircleRadialProfile_periodic data small)
    (by linarith : 0 < 1 - ‖data - standardCircleBanach‖)
    (nearCircleRadialProfile_lower data small) (nearCircleRadialProfile_upper data small)

end

end EulerNonuniqueness.Paper
