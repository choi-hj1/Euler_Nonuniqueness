import EulerNonuniqueness.Section6.ForcedDipoleQuadraticMoment

noncomputable section

open scoped NNReal

namespace EulerNonuniqueness.Section6

def twoDipoleResidualMomentVelocity (residual : FourPointConfiguration)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : ℂ :=
  ((residual 0 + residual 2) / 2 - (residual 1 + residual 3) / 2) *
      (firstSeparation - secondSeparation) +
    (firstCenter - secondCenter) * (residual 0 - residual 2 - (residual 1 - residual 3))

theorem twoDipoleResidualMomentVelocity_bound (residual : FourPointConfiguration)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ} {length : ℝ}
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (distanceLarge : 4 * length ≤ ‖firstCenter - secondCenter‖) :
    ‖twoDipoleResidualMomentVelocity residual firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      6 * ‖firstCenter - secondCenter‖ * ‖residual‖ := by
  have averageBound : ‖(residual 0 + residual 2) / 2 - (residual 1 + residual 3) / 2‖ ≤ 2 * ‖residual‖ :=
    (norm_sub_le _ _).trans (by linarith [residual_pair_average_bound residual 0 2,
      residual_pair_average_bound residual 1 3])
  have differenceBound : ‖residual 0 - residual 2 - (residual 1 - residual 3)‖ ≤ 4 * ‖residual‖ :=
    (norm_sub_le _ _).trans (by linarith [residual_pair_difference_bound residual 0 2,
      residual_pair_difference_bound residual 1 3])
  have separationBound : ‖firstSeparation - secondSeparation‖ ≤ 4 * length :=
    (norm_sub_le _ _).trans (by linarith)
  unfold twoDipoleResidualMomentVelocity
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  have control := add_le_add
    (mul_le_mul averageBound separationBound (norm_nonneg _) (by positivity))
    (mul_le_mul_of_nonneg_left differenceBound (norm_nonneg (firstCenter - secondCenter)))
  apply control.trans
  nlinarith [mul_le_mul_of_nonneg_right distanceLarge (norm_nonneg residual)]

theorem twoDipole_residual_centered_complex_moment_hasDerivAt
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℂ → ℂ} {residual : FourPointConfiguration} {coefficient time : ℝ}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target +
        external (twoDipoleConfiguration (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) target) + residual target) time) :
    HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current)))
      ((dipoleSelfVelocity coefficient (firstSeparation time) - dipoleSelfVelocity coefficient (secondSeparation time)) *
          (firstSeparation time - secondSeparation time) +
        twoDipoleComplexMomentCrossVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) +
        twoDipoleExternalMomentVelocity external (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time) +
        twoDipoleResidualMomentVelocity residual (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) time := by
  have centerDerivative := twoDipole_centers_actual_forced_equation equation
  have firstDerivative := (twoDipole_first_pair_forced_equations equation).2
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
        externalPairDifference external (secondCenter time) (secondSeparation time) +
        (residual 1 - residual 3)) time := by
    convert secondDerivative using 1 <;>
      simp [dipoleCrossRelativeVelocity, externalPairDifference, twoDipoleConfiguration] <;> ring
  have derivative := centerDerivative.mul (firstDerivative.sub secondDerivative')
  simp only [twoDipole_centered_complex_moment]
  convert derivative using 1
  dsimp [twoDipoleCenterRelativeVelocity, twoDipoleComplexMomentCrossVelocity,
    twoDipoleExternalMomentVelocity, twoDipoleExternalCenterCorrection, twoDipoleResidualMomentVelocity]
  ring

theorem twoDipole_residual_centered_complex_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {external : ℂ → ℂ} {residual : FourPointConfiguration}
    {region : Set ℂ} {strain : ℝ≥0} {frequency length time : ℝ} {direction : ℂ}
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
          (firstSeparation time) (secondSeparation time) target) + residual target) time) :
    ∃ velocity : ℂ, HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current))) velocity time ∧
      ‖velocity - (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2)‖ ≤
        10 * frequency * length * (‖firstSeparation time - (length : ℂ) * direction‖ +
          ‖secondSeparation time - (length : ℂ) * (-direction)‖) +
        320 * frequency * length ^ 4 / ‖firstCenter time - secondCenter time‖ ^ 2 +
        12 * (strain : ℝ) * ‖firstCenter time - secondCenter time‖ * length +
        6 * ‖firstCenter time - secondCenter time‖ * ‖residual‖ := by
  have derivative := twoDipole_residual_centered_complex_moment_hasDerivAt equation
  refine ⟨_, derivative, ?_⟩
  have selfControl := twoDipole_complex_moment_self_error frequency length frequencyPositive lengthPositive
    directionNorm firstLower secondLower firstUpper secondUpper
  have crossControl := twoDipoleComplexMomentCrossVelocity_bound (frequency * length ^ 2)
    lengthPositive firstUpper secondUpper distanceLarge
  rw [abs_of_pos (by positivity : 0 < frequency * length ^ 2)] at crossControl
  have externalControl := twoDipoleExternalMomentVelocity_bound lipschitz lengthPositive firstUpper secondUpper distanceLarge inside
  have residualControl := twoDipoleResidualMomentVelocity_bound residual firstUpper secondUpper distanceLarge
  have rearrange (self cross forcing residual ideal : ℂ) :
      self + cross + forcing + residual - ideal = ((self - ideal) + cross + forcing) + residual := by ring
  rw [rearrange]
  apply (norm_add_le _ _).trans
  apply (add_le_add_right (norm_add_le _ _) _).trans
  apply (add_le_add_right (add_le_add_right (norm_add_le _ _) _) _).trans
  convert add_le_add (add_le_add (add_le_add selfControl crossControl) externalControl) residualControl using 1 <;> ring

end EulerNonuniqueness.Section6
