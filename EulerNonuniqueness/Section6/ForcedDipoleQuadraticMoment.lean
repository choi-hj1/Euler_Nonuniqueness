import EulerNonuniqueness.Section6.DipoleQuadraticMoment
import EulerNonuniqueness.Section6.ForcedTwoDipoleDynamics

noncomputable section

open Set
open scoped NNReal

namespace EulerNonuniqueness.Section6

def twoDipoleExternalMomentVelocity (external : ℂ → ℂ)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : ℂ :=
  twoDipoleExternalCenterCorrection external 0 firstCenter secondCenter firstSeparation secondSeparation *
      (firstSeparation - secondSeparation) +
    (firstCenter - secondCenter) *
      (externalPairDifference external firstCenter firstSeparation -
        externalPairDifference external secondCenter secondSeparation)

theorem twoDipoleExternalMomentVelocity_bound {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0}
    (lipschitz : LipschitzOnWith strain external region)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (distanceLarge : 4 * length ≤ ‖firstCenter - secondCenter‖)
    (inside : ∀ target, twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation target ∈ region) :
    ‖twoDipoleExternalMomentVelocity external firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      12 * (strain : ℝ) * ‖firstCenter - secondCenter‖ * length := by
  have separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖firstCenter - secondCenter‖ := by linarith
  have centerControl := twoDipoleExternalCenterCorrection_bound lipschitz 0 inside separationBound
  simp only [norm_zero, mul_zero, add_zero] at centerControl
  have firstControl := externalPairDifference_bound lipschitz (inside 0) (inside 2)
  have secondControl := externalPairDifference_bound lipschitz (inside 1) (inside 3)
  have relativeControl : ‖externalPairDifference external firstCenter firstSeparation -
      externalPairDifference external secondCenter secondSeparation‖ ≤ 4 * (strain : ℝ) * length := by
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ (strain : ℝ) * ‖firstSeparation‖ + (strain : ℝ) * ‖secondSeparation‖ := add_le_add firstControl secondControl
      _ ≤ (strain : ℝ) * (2 * length) + (strain : ℝ) * (2 * length) := by gcongr
      _ = _ := by ring
  have separationControl : ‖firstSeparation - secondSeparation‖ ≤ 4 * length :=
    (norm_sub_le _ _).trans (by linarith)
  unfold twoDipoleExternalMomentVelocity
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (2 * (strain : ℝ) * ‖firstCenter - secondCenter‖) * (4 * length) +
        ‖firstCenter - secondCenter‖ * (4 * (strain : ℝ) * length) :=
      add_le_add (mul_le_mul centerControl separationControl (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left relativeControl (norm_nonneg _))
    _ = _ := by ring

theorem twoDipole_forced_centered_complex_moment_hasDerivAt
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℂ → ℂ} {coefficient time : ℝ}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target)) time) :
    HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current)))
      ((dipoleSelfVelocity coefficient (firstSeparation time) - dipoleSelfVelocity coefficient (secondSeparation time)) *
          (firstSeparation time - secondSeparation time) +
        twoDipoleComplexMomentCrossVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) +
        twoDipoleExternalMomentVelocity external (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) time := by
  have withResidual : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + (0 : FourPointConfiguration) target) time := by
    simpa only [Pi.zero_apply, add_zero] using equation
  have centerDerivative := twoDipole_centers_actual_forced_equation withResidual
  have firstDerivative := (twoDipole_first_pair_forced_equations withResidual).2
  have secondDerivative := (equation 1).sub (equation 3)
  rw [fourPointField_twoDipoles] at secondDerivative
  have secondFunction : (fun current =>
      twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 1 -
      twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) 3) = secondSeparation := by
    funext current
    simp [twoDipoleConfiguration]
  rw [secondFunction] at secondDerivative
  have secondDerivative' : HasDerivAt secondSeparation
      (dipoleCrossRelativeVelocity coefficient (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time) +
        externalPairDifference external (secondCenter time) (secondSeparation time)) time := by
    convert secondDerivative using 1 <;>
      simp [dipoleCrossRelativeVelocity, externalPairDifference, twoDipoleConfiguration] <;> ring
  have derivative := centerDerivative.mul (firstDerivative.sub secondDerivative')
  simp only [twoDipole_centered_complex_moment]
  convert derivative using 1
  dsimp [twoDipoleCenterRelativeVelocity, twoDipoleComplexMomentCrossVelocity,
    twoDipoleExternalMomentVelocity, twoDipoleExternalCenterCorrection]
  ring

theorem twoDipole_forced_centered_complex_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℂ → ℂ} {region : Set ℂ} {strain : ℝ≥0}
    {frequency length time : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstLower : length / 2 ≤ ‖firstSeparation time‖) (secondLower : length / 2 ≤ ‖secondSeparation time‖)
    (firstUpper : ‖firstSeparation time‖ ≤ 2 * length) (secondUpper : ‖secondSeparation time‖ ≤ 2 * length)
    (distanceLarge : 4 * length ≤ ‖firstCenter time - secondCenter time‖)
    (lipschitz : LipschitzOnWith strain external region)
    (inside : ∀ target, twoDipoleConfiguration (firstCenter time) (secondCenter time)
      (firstSeparation time) (secondSeparation time) target ∈ region)
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target)) time) :
    ∃ velocity : ℂ, HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current))) velocity time ∧
      ‖velocity - (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2)‖ ≤
        10 * frequency * length * (‖firstSeparation time - (length : ℂ) * direction‖ +
          ‖secondSeparation time - (length : ℂ) * (-direction)‖) +
        320 * frequency * length ^ 4 / ‖firstCenter time - secondCenter time‖ ^ 2 +
        12 * (strain : ℝ) * ‖firstCenter time - secondCenter time‖ * length := by
  have derivative := twoDipole_forced_centered_complex_moment_hasDerivAt equation
  refine ⟨_, derivative, ?_⟩
  have selfControl := twoDipole_complex_moment_self_error frequency length frequencyPositive lengthPositive
    directionNorm firstLower secondLower firstUpper secondUpper
  have crossControl := twoDipoleComplexMomentCrossVelocity_bound (frequency * length ^ 2)
    lengthPositive firstUpper secondUpper distanceLarge
  rw [abs_of_pos (by positivity : 0 < frequency * length ^ 2)] at crossControl
  have externalControl := twoDipoleExternalMomentVelocity_bound lipschitz lengthPositive firstUpper secondUpper distanceLarge inside
  have rearrange (self cross forcing ideal : ℂ) : self + cross + forcing - ideal = (self - ideal) + cross + forcing := by ring
  rw [rearrange]
  apply (norm_add_le _ _).trans
  apply (add_le_add_right (norm_add_le _ _) _).trans
  convert add_le_add (add_le_add selfControl crossControl) externalControl using 1 <;> ring

end EulerNonuniqueness.Section6
