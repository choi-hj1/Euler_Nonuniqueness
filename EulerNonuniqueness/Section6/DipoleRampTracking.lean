import EulerNonuniqueness.Section6.DipoleQuadraticMoment
import EulerNonuniqueness.Section6.ContinuedDipoleSeparation

noncomputable section

open Set

namespace EulerNonuniqueness.Section6

theorem twoDipole_continued_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length initialDistance horizon initialError : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (initialErrorNonnegative : 0 ≤ initialError) (initialErrorSmall : initialError ≤ 1 / 32)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target) time)
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
      frequency * length ^ 2 * (20 * initialError + 83200 / initialDistance ^ 2) * time := by
  have continuation := twoDipole_continued_separation frequencyPositive lengthPositive directionNorm
    initialDistanceLarge horizonNonnegative equation
    (firstInitial.trans (by nlinarith)) (secondInitial.trans (by nlinarith)) initialProjection initialUpper
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
  have firstTracking := twoDipole_first_separation_tracking ((length : ℂ) * direction)
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) horizonNonnegative equation
    (fun time member => (firstBounds time member).2) (fun time member => (secondBounds time member).2) distanceBounds
  have secondTracking := twoDipole_second_separation_tracking ((length : ℂ) * (-direction))
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) horizonNonnegative equation
    (fun time member => (firstBounds time member).2) (fun time member => (secondBounds time member).2) distanceBounds
  let slope := -4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2
  let corrected := fun time => fourPointCenteredComplexMoment
    (twoDipoleConfiguration (firstCenter time) (secondCenter time) (firstSeparation time) (secondSeparation time)) -
      slope * (time : ℂ)
  let bound := frequency * length ^ 2 * (20 * initialError + 83200 / initialDistance ^ 2)
  have derivativeControl (time : ℝ) (member : time ∈ Icc 0 horizon) :
      DifferentiableAt ℝ corrected time ∧ ‖deriv corrected time‖ ≤ bound := by
    have positiveProduct : 0 ≤ length * (frequency * time) :=
      mul_nonneg lengthPositive.le (mul_nonneg frequencyPositive.le member.1)
    have distanceLower : length * initialDistance / 2 ≤ ‖firstCenter time - secondCenter time‖ := by
      have control := (continuation time member).2.2.1
      nlinarith
    have distanceLarge : 4 * length ≤ ‖firstCenter time - secondCenter time‖ := by
      nlinarith
    obtain ⟨velocity, derivative, control⟩ := twoDipole_centered_complex_moment_ramp frequencyPositive lengthPositive
      directionNorm (firstBounds time member).1 (secondBounds time member).1
      (firstBounds time member).2 (secondBounds time member).2 distanceLarge (equation time member)
    have correctedDerivative : HasDerivAt corrected (velocity - slope) time := by
      exact derivative.sub (by simpa using ((hasDerivAt_id time).ofReal_comp.const_mul slope))
    refine ⟨correctedDerivative.differentiableAt, ?_⟩
    rw [correctedDerivative.deriv]
    have separationControl : ‖firstSeparation time - (length : ℂ) * direction‖ +
        ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤
        2 * initialError * length + 8192 * length / initialDistance ^ 2 := by
      calc
        _ ≤ (‖firstSeparation 0 - (length : ℂ) * direction‖ + 4096 * length / initialDistance ^ 2) +
            (‖secondSeparation 0 - (length : ℂ) * (-direction)‖ + 4096 * length / initialDistance ^ 2) :=
          add_le_add (firstTracking time member) (secondTracking time member)
        _ ≤ (initialError * length + 4096 * length / initialDistance ^ 2) +
            (initialError * length + 4096 * length / initialDistance ^ 2) := by gcongr
        _ = _ := by ring
    have distancePositive : 0 < length * initialDistance / 2 := by positivity
    have squareControl := pow_le_pow_left₀ distancePositive.le distanceLower 2
    have crossControl : 320 * frequency * length ^ 4 / ‖firstCenter time - secondCenter time‖ ^ 2 ≤
        1280 * frequency * length ^ 2 / initialDistance ^ 2 := by
      calc
        _ ≤ 320 * frequency * length ^ 4 / (length * initialDistance / 2) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos distancePositive) squareControl
        _ = _ := by
          field_simp [lengthPositive.ne', (show initialDistance ≠ 0 by linarith)]
          ring
    apply control.trans
    have estimate := add_le_add
      (mul_le_mul_of_nonneg_left separationControl (by positivity : 0 ≤ 10 * frequency * length)) crossControl
    convert estimate using 1 <;> dsimp [bound] <;> ring
  intro time member
  have estimate := (convex_Icc (0 : ℝ) horizon).norm_image_sub_le_of_norm_deriv_le
    (fun current currentInside => (derivativeControl current currentInside).1)
    (fun current currentInside => (derivativeControl current currentInside).2)
    (left_mem_Icc.mpr horizonNonnegative) member
  have identity : corrected time - corrected 0 =
      fourPointCenteredComplexMoment (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) -
      fourPointCenteredComplexMoment (twoDipoleConfiguration (firstCenter 0) (secondCenter 0)
        (firstSeparation 0) (secondSeparation 0)) - slope * (time : ℂ) := by
    dsimp [corrected]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    ring
  rw [identity] at estimate
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg member.1] using estimate

end EulerNonuniqueness.Section6
