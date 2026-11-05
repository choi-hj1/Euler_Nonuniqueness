import EulerNonuniqueness.Section6.ForcedTwoDipoleDynamics

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem dipole_velocity_outward_of_ideal_error (frequency length : ℝ) {direction velocity : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (errorBound : ‖velocity - (-2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction)‖ ≤ frequency * length) :
    frequency * length ≤ (Complex.I * star direction * velocity).re ∧ ‖velocity‖ ≤ 3 * frequency * length := by
  let ideal := -2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have idealProjection : Complex.I * star direction * ideal = ((2 * frequency * length : ℝ) : ℂ) := by
    calc
      _ = (-2 * (Complex.I * Complex.I) * (frequency : ℂ) * (length : ℂ)) * (star direction * direction) := by
        dsimp [ideal]
        ring
      _ = _ := by rw [Complex.I_mul_I, unitProduct]; push_cast; ring
  have projectionError : |(Complex.I * star direction * velocity).re - 2 * frequency * length| ≤ frequency * length := by
    have realProjection := congrArg Complex.re idealProjection
    simp only [Complex.ofReal_re] at realProjection
    rw [← realProjection, ← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul] using errorBound
  have idealNorm : ‖ideal‖ = 2 * frequency * length := by
    simp [ideal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive,
      abs_of_pos lengthPositive, directionNorm]
  have triangle := norm_add_le (velocity - ideal) ideal
  rw [sub_add_cancel, idealNorm] at triangle
  exact ⟨by linarith [(abs_le.mp projectionError).1], by linarith⟩

theorem twoDipoleExternalCenterCorrection_small
    {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0} {residual : FourPointConfiguration}
    {frequency length initialDistance horizon time error : ℝ}
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (initialDistanceLarge : 16 ≤ initialDistance)
    (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon)
    (forcingSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (lipschitz : LipschitzOnWith strain external region)
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region)
    (residualBound : ‖residual‖ ≤ error * length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (distanceLower : length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter - secondCenter‖)
    (distanceUpper : ‖firstCenter - secondCenter‖ ≤ 4 * length * (initialDistance + frequency * time)) :
    ‖twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      frequency * length / 2 := by
  have productNonnegative := mul_nonneg frequencyPositive.le timeNonnegative
  have separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖firstCenter - secondCenter‖ := by nlinarith
  have control := twoDipoleExternalCenterCorrection_bound lipschitz residual inside separationBound
  have scaledSmall := mul_le_mul_of_nonneg_left forcingSmall frequencyPositive.le
  have identity : frequency * (8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency) =
      8 * (strain : ℝ) * (frequency * horizon + initialDistance) + 2 * error := by
    field_simp [frequencyPositive.ne'] <;> ring <;> simp
  rw [identity] at scaledSmall
  have coefficientBound : 8 * (strain : ℝ) * (initialDistance + frequency * time) + 2 * error ≤ frequency / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left timeBound (mul_nonneg strain.coe_nonneg frequencyPositive.le)]
  have lengthScaled := mul_le_mul_of_nonneg_left coefficientBound lengthPositive.le
  have distanceScaled := mul_le_mul_of_nonneg_left distanceUpper (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) strain.coe_nonneg)
  nlinarith

theorem twoDipole_forced_center_outward
    {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0} {residual : FourPointConfiguration}
    {frequency length initialDistance horizon time error : ℝ}
    {direction firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 64 ≤ initialDistance) (timeNonnegative : 0 ≤ time) (timeBound : time ≤ horizon)
    (forcingSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (lipschitz : LipschitzOnWith strain external region)
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region)
    (residualBound : ‖residual‖ ≤ error * length)
    (firstError : ‖firstSeparation - (length : ℂ) * direction‖ ≤ length / 16)
    (secondError : ‖secondSeparation - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (distanceLower : length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter - secondCenter‖)
    (distanceUpper : ‖firstCenter - secondCenter‖ ≤ 4 * length * (initialDistance + frequency * time)) :
    let velocity := twoDipoleCenterRelativeVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation +
      twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation
    frequency * length ≤ (Complex.I * star direction * velocity).re ∧ ‖velocity‖ ≤ 3 * frequency * length := by
  dsimp only
  obtain ⟨_, firstUpper⟩ := dipole_separation_norm_bounds length lengthPositive directionNorm firstError
  obtain ⟨_, secondUpper⟩ := dipole_separation_norm_bounds length lengthPositive (by simpa using directionNorm) secondError
  have centerDistance : 16 * length ≤ ‖firstCenter - secondCenter‖ := by
    nlinarith [mul_nonneg frequencyPositive.le timeNonnegative]
  have internal := twoDipoleCenterRelativeVelocity_ideal_error frequency length frequencyPositive lengthPositive directionNorm
    firstError secondError centerDistance
  have correction := twoDipoleExternalCenterCorrection_small frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance)
    timeNonnegative timeBound forcingSmall lipschitz inside residualBound firstUpper secondUpper distanceLower distanceUpper
  apply dipole_velocity_outward_of_ideal_error frequency length frequencyPositive lengthPositive directionNorm
  have identity :
      twoDipoleCenterRelativeVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation +
          twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation -
          (-2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction) =
      (twoDipoleCenterRelativeVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation -
        (-2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction)) +
        twoDipoleExternalCenterCorrection external residual firstCenter secondCenter firstSeparation secondSeparation := by ring
  rw [identity]
  exact (norm_add_le _ _).trans (by linarith)

end EulerNonuniqueness.Section6
