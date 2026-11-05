import EulerNonuniqueness.Section6.ForcedDipoleQuadraticMoment
import EulerNonuniqueness.Section6.ContinuedForcedDipoleSeparation

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

theorem complex_affine_tracking_of_derivative_bound {trajectory : ℝ → ℂ} {slope : ℂ} {bound horizon : ℝ}
    (horizonNonnegative : 0 ≤ horizon)
    (control : ∀ time ∈ Icc 0 horizon, ∃ velocity : ℂ, HasDerivAt trajectory velocity time ∧ ‖velocity - slope‖ ≤ bound) :
    ∀ time ∈ Icc 0 horizon, ‖trajectory time - trajectory 0 - slope * (time : ℂ)‖ ≤ bound * time := by
  let corrected := fun time => trajectory time - slope * (time : ℂ)
  have derivativeControl (time : ℝ) (member : time ∈ Icc 0 horizon) :
      DifferentiableAt ℝ corrected time ∧ ‖deriv corrected time‖ ≤ bound := by
    obtain ⟨velocity, derivative, estimate⟩ := control time member
    have correctedDerivative : HasDerivAt corrected (velocity - slope) time :=
      derivative.sub (by simpa using ((hasDerivAt_id time).ofReal_comp.const_mul slope))
    exact ⟨correctedDerivative.differentiableAt, by simpa only [correctedDerivative.deriv] using estimate⟩
  intro time member
  have estimate := (convex_Icc (0 : ℝ) horizon).norm_image_sub_le_of_norm_deriv_le
    (fun current currentInside => (derivativeControl current currentInside).1)
    (fun current currentInside => (derivativeControl current currentInside).2)
    (left_mem_Icc.mpr horizonNonnegative) member
  have identity : corrected time - corrected 0 = trajectory time - trajectory 0 - slope * (time : ℂ) := by
    dsimp [corrected]
    simp only [Complex.ofReal_zero, mul_zero, sub_zero]
    ring
  rw [identity] at estimate
  simpa only [sub_zero, Real.norm_eq_abs, abs_of_nonneg member.1] using estimate

theorem twoDipole_forced_continued_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℝ → ℂ → ℂ} {region : ℝ → Set ℂ}
    {frequency length initialDistance horizon initialError : ℝ} {direction : ℂ} {strain : ℝ≥0}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (initialDistanceLarge : 512 ≤ initialDistance) (horizonNonnegative : 0 ≤ horizon)
    (initialErrorSmall : initialError ≤ 1 / 64)
    (relativeSmall : 64 * (strain : ℝ) * horizon ≤ 1)
    (centerSmall : 8 * (strain : ℝ) * (horizon + initialDistance / frequency) ≤ 1 / 2)
    (equation : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2)
        (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) target + external time
            (twoDipoleConfiguration (firstCenter time) (secondCenter time)
              (firstSeparation time) (secondSeparation time) target)) time)
    (externalLipschitz : ∀ time ∈ Icc 0 horizon, LipschitzOnWith strain (external time) (region time))
    (inside : ∀ time ∈ Icc 0 horizon, ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region time)
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
        76 * frequency * (strain : ℝ) * length ^ 2 * horizon + 36 * (strain : ℝ) * length ^ 2 * initialDistance) * time := by
  have withResidual : ∀ time ∈ Icc 0 horizon, ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target + external time
          (twoDipoleConfiguration (firstCenter time) (secondCenter time)
            (firstSeparation time) (secondSeparation time) target) + (0 : FourPointConfiguration) target) time := by
    simpa only [Pi.zero_apply, add_zero] using equation
  have continuation := twoDipole_forced_continued_separation frequencyPositive lengthPositive directionNorm
    initialDistanceLarge horizonNonnegative (error := 0) le_rfl (by simpa using relativeSmall)
    (by simpa using centerSmall) withResidual externalLipschitz inside (by simp)
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
  have tracking := twoDipole_forced_separation_tracking ((length : ℂ) * direction) ((length : ℂ) * (-direction))
    frequencyPositive lengthPositive (by linarith : 16 ≤ initialDistance) withResidual externalLipschitz inside
    (error := 0) (by simp) (fun time member => (firstBounds time member).2)
    (fun time member => (secondBounds time member).2) distanceBounds
  apply complex_affine_tracking_of_derivative_bound horizonNonnegative
  intro time member
  have positiveProduct : 0 ≤ length * (frequency * time) :=
    mul_nonneg lengthPositive.le (mul_nonneg frequencyPositive.le member.1)
  have distanceLower : length * initialDistance / 2 ≤ ‖firstCenter time - secondCenter time‖ := by
    have control := (continuation time member).2.2.1
    nlinarith
  have distanceLarge : 4 * length ≤ ‖firstCenter time - secondCenter time‖ := by nlinarith
  obtain ⟨velocity, derivative, control⟩ := twoDipole_forced_centered_complex_moment_ramp frequencyPositive lengthPositive
    directionNorm (firstBounds time member).1 (secondBounds time member).1
    (firstBounds time member).2 (secondBounds time member).2 distanceLarge
    (externalLipschitz time member) (inside time member) (equation time member)
  refine ⟨velocity, derivative, control.trans ?_⟩
  have separationControl : ‖firstSeparation time - (length : ℂ) * direction‖ +
      ‖secondSeparation time - (length : ℂ) * (-direction)‖ ≤
      2 * initialError * length + 8192 * length / initialDistance ^ 2 + 4 * (strain : ℝ) * length * horizon := by
    have first := (tracking time member).1
    have second := (tracking time member).2
    simp only [add_zero] at first second
    calc
      _ ≤ (initialError * length + 4096 * length / initialDistance ^ 2 + 2 * (strain : ℝ) * length * time) +
          (initialError * length + 4096 * length / initialDistance ^ 2 + 2 * (strain : ℝ) * length * time) := by linarith
      _ ≤ (initialError * length + 4096 * length / initialDistance ^ 2 + 2 * (strain : ℝ) * length * horizon) +
          (initialError * length + 4096 * length / initialDistance ^ 2 + 2 * (strain : ℝ) * length * horizon) := by
        gcongr <;> exact member.2
      _ = _ := by ring
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
  have distanceUpper : ‖firstCenter time - secondCenter time‖ ≤ 3 * length * (initialDistance + frequency * horizon) :=
    (continuation time member).2.2.2.trans (by gcongr; exact member.2)
  have externalControl : 12 * (strain : ℝ) * ‖firstCenter time - secondCenter time‖ * length ≤
      36 * (strain : ℝ) * length ^ 2 * (initialDistance + frequency * horizon) := by
    calc
      _ ≤ 12 * (strain : ℝ) * (3 * length * (initialDistance + frequency * horizon)) * length := by gcongr
      _ = _ := by ring
  have estimate := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left separationControl (by positivity : 0 ≤ 10 * frequency * length)) crossControl)
    externalControl
  convert estimate using 1 <;> ring

end EulerNonuniqueness.Section6
