import EulerNonuniqueness.Section6.ForcedDipoleRampTracking

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem fourPointArithmeticCenter_twoDipoles (firstCenter secondCenter firstSeparation secondSeparation : ℂ) :
    fourPointArithmeticCenter (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) =
      (firstCenter + secondCenter) / 2 := by
  simp [fourPointArithmeticCenter, twoDipoleConfiguration, Fin.sum_univ_succ]
  ring

theorem twoDipole_point_midpoint_velocity_bound
    {firstCenter secondCenter firstSeparation secondSeparation direction : ℂ} {frequency length : ℝ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstError : ‖firstSeparation - (length : ℂ) * direction‖ ≤ length / 16)
    (secondError : ‖secondSeparation - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (distanceLarge : 16 * length ≤ ‖firstCenter - secondCenter‖) :
    ‖fourPointArithmeticCenter (fourPointField (frequency * length ^ 2)
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation))‖ ≤
        5 * frequency * length / 32 := by
  have negativeNorm : ‖-direction‖ = 1 := by simpa only [norm_neg] using directionNorm
  obtain ⟨firstLower, firstUpper⟩ := dipole_separation_norm_bounds length lengthPositive directionNorm firstError
  obtain ⟨secondLower, secondUpper⟩ := dipole_separation_norm_bounds length lengthPositive negativeNorm secondError
  let ideal := -Complex.I * (frequency : ℂ) * (length : ℂ) * direction
  have firstSelf : ‖dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal‖ ≤
      frequency * length / 8 :=
    (dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive directionNorm firstLower).trans
      (by nlinarith [mul_le_mul_of_nonneg_left firstError (show 0 ≤ 2 * frequency by positivity)])
  have secondSelf : ‖dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal)‖ ≤
      frequency * length / 8 := by
    have control := dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive negativeNorm secondLower
    have identity : -Complex.I * (frequency : ℂ) * (length : ℂ) * (-direction) = -ideal := by
      dsimp only [ideal]
      ring
    rw [identity] at control
    exact control.trans (by nlinarith [mul_le_mul_of_nonneg_left secondError (show 0 ≤ 2 * frequency by positivity)])
  have selfSum : ‖dipoleSelfVelocity (frequency * length ^ 2) firstSeparation +
      dipoleSelfVelocity (frequency * length ^ 2) secondSeparation‖ ≤ frequency * length / 4 := by
    have identity : dipoleSelfVelocity (frequency * length ^ 2) firstSeparation +
        dipoleSelfVelocity (frequency * length ^ 2) secondSeparation =
        (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal) +
          (dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal)) := by ring
    rw [identity]
    exact (norm_add_le _ _).trans (by linarith)
  have firstCross := dipoleCrossCenterVelocity_small frequency length frequencyPositive lengthPositive
    secondUpper firstUpper distanceLarge
  have secondCross := dipoleCrossCenterVelocity_small frequency length frequencyPositive lengthPositive
    firstUpper secondUpper (show 16 * length ≤ ‖secondCenter - firstCenter‖ by
      simpa only [norm_sub_rev] using distanceLarge)
  have fieldIdentity : fourPointArithmeticCenter (fourPointField (frequency * length ^ 2)
      (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation)) =
      ((dipoleSelfVelocity (frequency * length ^ 2) firstSeparation +
        dipoleSelfVelocity (frequency * length ^ 2) secondSeparation) +
        (dipoleCrossCenterVelocity (frequency * length ^ 2) secondCenter firstCenter secondSeparation firstSeparation +
          dipoleCrossCenterVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation)) / 2 := by
    rw [fourPointField_twoDipoles]
    simp [fourPointArithmeticCenter, dipoleSelfVelocity, dipoleCrossCenterVelocity, Fin.sum_univ_succ]
    ring
  rw [fieldIdentity, norm_div, Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  have crossTriangle := norm_add_le
    (dipoleCrossCenterVelocity (frequency * length ^ 2) secondCenter firstCenter secondSeparation firstSeparation)
    (dipoleCrossCenterVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation)
  exact (norm_add_le _ _).trans (by linarith)

theorem twoDipole_forced_midpoint_drift
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration}
    {frequency length horizon error externalBound : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (horizonNonnegative : 0 ≤ horizon) (errorNonnegative : 0 ≤ error) (externalNonnegative : 0 ≤ externalBound)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target + external time
            (twoDipoleConfiguration (firstCenter time) (secondCenter time)
              (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (firstError : ∀ time ∈ Icc 0 horizon,
      ‖firstSeparation time - (length : ℂ) * direction‖ ≤ length / 16)
    (secondError : ∀ time ∈ Icc 0 horizon,
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (distanceLarge : ∀ time ∈ Icc 0 horizon, 16 * length ≤ ‖firstCenter time - secondCenter time‖)
    (externalControl : ∀ time ∈ Icc 0 horizon, ∀ target,
      ‖external time (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) target)‖ ≤ externalBound)
    (residualControl : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length) :
    ∀ time ∈ Icc 0 horizon,
      ‖(firstCenter time + secondCenter time) / 2 - (firstCenter 0 + secondCenter 0) / 2‖ ≤
        (5 * frequency * length / 32 + externalBound + error * length) * time := by
  have control := complex_affine_tracking_of_derivative_bound (slope := 0)
    (bound := 5 * frequency * length / 32 + externalBound + error * length) horizonNonnegative (by
    intro time member
    let forcing : FourPointConfiguration := fun target => external time
      (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) target) + residual time target
    have derivative := fourPointArithmeticCenter_forced_hasDerivAt (forcing := forcing)
      (fun target => by simpa only [forcing, add_assoc] using equation time member target)
    simp only [fourPointArithmeticCenter_twoDipoles] at derivative
    refine ⟨_, derivative, ?_⟩
    rw [sub_zero]
    have forcingControl : ‖forcing‖ ≤ externalBound + error * length := by
      apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ externalBound + error * length)).mpr
      intro target
      exact (norm_add_le _ _).trans (add_le_add (externalControl time member target)
        ((norm_le_pi_norm (residual time) target).trans (residualControl time member)))
    exact (norm_add_le _ _).trans (by
      have pointControl := twoDipole_point_midpoint_velocity_bound frequencyPositive lengthPositive directionNorm
        (firstError time member) (secondError time member) (distanceLarge time member)
      have averageControl := (fourPointArithmeticCenter_norm_le forcing).trans forcingControl
      linarith))
  simpa only [zero_mul, sub_zero] using control

end EulerNonuniqueness.Section6
