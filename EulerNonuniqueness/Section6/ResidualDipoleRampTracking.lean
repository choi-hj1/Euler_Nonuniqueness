import EulerNonuniqueness.Section6.ResidualDipoleQuadraticMoment
import EulerNonuniqueness.Section6.ForcedDipoleRampTracking

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem twoDipole_residual_continued_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {residual : ℝ → FourPointConfiguration} {region : ℝ → Set ℂ}
    {frequency length initialDistance horizon initialError error : ℝ} {direction : ℂ} {strain : ℝ≥0}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (initialErrorSmall : initialError ≤ 1 / 64) (errorNonnegative : 0 ≤ error)
    (relativeSmall : 64 * ((strain : ℝ) + error) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) + 2 * error / frequency ≤ 1 / 2)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target + external time
            (twoDipoleConfiguration (firstCenter time) (secondCenter time)
              (firstSeparation time) (secondSeparation time) target) + residual time target) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
    (residualBound : ∀ time ∈ Icc 0 horizon, ‖residual time‖ ≤ error * length)
    (firstInitial : ‖firstSeparation 0 - (length : ℂ) * direction‖ ≤ initialError * length)
    (secondInitial : ‖secondSeparation 0 - (length : ℂ) * (-direction)‖ ≤ initialError * length)
    (initialProjection : (3 / 4 : ℝ) * length * initialDistance ≤
      (Complex.I * star direction * (firstCenter 0 - secondCenter 0)).re)
    (initialUpper : ‖firstCenter 0 - secondCenter 0‖ ≤ (5 / 4 : ℝ) * length * initialDistance) :
    ∀ time ∈ Icc 0 horizon,
      ‖fourPointCenteredComplexMoment (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) -
        fourPointCenteredComplexMoment (twoDipoleConfiguration (firstCenter 0) (secondCenter 0)
          (firstSeparation 0) (secondSeparation 0)) -
        (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2) * (time : ℂ)‖ ≤
      (20 * frequency * length ^ 2 * initialError + 83200 * frequency * length ^ 2 / initialDistance ^ 2 +
        76 * frequency * ((strain : ℝ) + error) * length ^ 2 * horizon +
        36 * ((strain : ℝ) + error) * length ^ 2 * initialDistance) * time := by
  have continuation := twoDipole_forced_continued_separation frequencyPositive lengthPositive directionNorm
    initialDistanceLarge horizonNonnegative errorNonnegative relativeSmall centerSmall equation externalLipschitz
    inside residualBound (firstInitial.trans (by nlinarith)) (secondInitial.trans (by nlinarith))
    initialProjection initialUpper
  have firstBounds (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    dipole_separation_norm_bounds length lengthPositive directionNorm (continuation time member).1
  have secondBounds (time : ℝ) (member : time ∈ Icc 0 horizon) :=
    dipole_separation_norm_bounds length lengthPositive
      (show ‖-direction‖ = 1 by simpa only [norm_neg] using directionNorm) (continuation time member).2.1
  have distanceBounds (time : ℝ) (member : time ∈ Icc 0 horizon) :
      length * (initialDistance + frequency * time) / 4 ≤ ‖firstCenter time - secondCenter time‖ := by
    have control := (continuation time member).2.2.1
    have productNonnegative : 0 ≤ length * (initialDistance + frequency * time) :=
      mul_nonneg lengthPositive.le (by nlinarith [mul_nonneg frequencyPositive.le member.1])
    linarith
  have tracking := twoDipole_forced_separation_tracking ((length : ℂ) * direction) ((length : ℂ) * (-direction))
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) equation externalLipschitz inside
    residualBound (fun time member => (firstBounds time member).2)
    (fun time member => (secondBounds time member).2) distanceBounds
  apply complex_affine_tracking_of_derivative_bound horizonNonnegative
  intro time member
  have positiveProduct : 0 ≤ length * (frequency * time) :=
    mul_nonneg lengthPositive.le (mul_nonneg frequencyPositive.le member.1)
  have distanceLower : length * initialDistance / 2 ≤ ‖firstCenter time - secondCenter time‖ := by
    have control := (continuation time member).2.2.1
    nlinarith
  have distanceLarge : 4 * length ≤ ‖firstCenter time - secondCenter time‖ := by nlinarith
  obtain ⟨velocity, derivative, control⟩ := twoDipole_residual_centered_complex_moment_ramp
    frequencyPositive lengthPositive directionNorm (firstBounds time member).1 (secondBounds time member).1
    (firstBounds time member).2 (secondBounds time member).2 distanceLarge
    (externalLipschitz time member) (inside time member) (equation time member)
  refine ⟨velocity, derivative, control.trans ?_⟩
  have separationControl : ‖firstSeparation time - (length : ℂ) * direction‖ +
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤
      2 * initialError * length + 8192 * length / initialDistance ^ 2 +
        4 * ((strain : ℝ) + error) * length * horizon := by
    have first := (tracking time member).1
    have second := (tracking time member).2
    have rateNonnegative : 0 ≤ ((strain : ℝ) + error) * length :=
      mul_nonneg (add_nonneg strain.coe_nonneg errorNonnegative) lengthPositive.le
    have firstControl := first.trans (add_le_add_right
      (add_le_add_right firstInitial (4096 * length / initialDistance ^ 2))
      (2 * ((strain : ℝ) + error) * length * time))
    have secondControl := second.trans (add_le_add_right
      (add_le_add_right secondInitial (4096 * length / initialDistance ^ 2))
      (2 * ((strain : ℝ) + error) * length * time))
    calc
      _ ≤ (initialError * length + 4096 * length / initialDistance ^ 2 +
          2 * ((strain : ℝ) + error) * length * time) +
          (initialError * length + 4096 * length / initialDistance ^ 2 +
          2 * ((strain : ℝ) + error) * length * time) := add_le_add firstControl secondControl
      _ = 2 * initialError * length + 8192 * length / initialDistance ^ 2 +
          4 * ((strain : ℝ) + error) * length * time := by ring
      _ ≤ _ := by gcongr; exact member.2
  have radiusPositive : 0 < length * initialDistance / 2 := by positivity
  have crossControl : 320 * frequency * length ^ 4 / ‖firstCenter time - secondCenter time‖ ^ 2 ≤
      1280 * frequency * length ^ 2 / initialDistance ^ 2 := by
    calc
      _ ≤ 320 * frequency * length ^ 4 / (length * initialDistance / 2) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos radiusPositive)
          (pow_le_pow_left₀ radiusPositive.le distanceLower 2)
      _ = _ := by
        field_simp [lengthPositive.ne', (show initialDistance ≠ 0 by linarith)]
        ring
  have distanceUpper : ‖firstCenter time - secondCenter time‖ ≤
      3 * length * (initialDistance + frequency * horizon) :=
    (continuation time member).2.2.2.trans (by gcongr; exact member.2)
  have combinedControl : 12 * (strain : ℝ) * ‖firstCenter time - secondCenter time‖ * length +
        6 * ‖firstCenter time - secondCenter time‖ * ‖residual time‖ ≤
      36 * ((strain : ℝ) + error) * length ^ 2 * (initialDistance + frequency * horizon) := by
    have residualControl := mul_le_mul_of_nonneg_left (residualBound time member)
      (show 0 ≤ 6 * ‖firstCenter time - secondCenter time‖ by positivity)
    have distanceControl := mul_le_mul_of_nonneg_right distanceUpper
      (show 0 ≤ 12 * ((strain : ℝ) + error) * length by positivity)
    nlinarith [mul_nonneg errorNonnegative (norm_nonneg (firstCenter time - secondCenter time))]
  have estimate := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left separationControl (by positivity : 0 ≤ 10 * frequency * length)) crossControl)
    combinedControl
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
