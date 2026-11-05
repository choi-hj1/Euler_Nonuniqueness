import EulerNonuniqueness.Section6.DipoleMomentCancellation
import EulerNonuniqueness.Section6.DipoleDirection

noncomputable section

namespace EulerNonuniqueness.Section6

def fourPointCenteredComplexMoment (positions : FourPointConfiguration) : ℂ :=
  ∑ target : Fin 4, (fourPointSign target : ℂ) *
    (positions target - fourPointArithmeticCenter positions) ^ 2

theorem twoDipole_centered_complex_moment (firstCenter secondCenter firstSeparation secondSeparation : ℂ) :
    fourPointCenteredComplexMoment (twoDipoleConfiguration firstCenter secondCenter firstSeparation secondSeparation) =
      (firstCenter - secondCenter) * (firstSeparation - secondSeparation) := by
  simp [fourPointCenteredComplexMoment, fourPointArithmeticCenter, fourPointSign,
    Fin.sum_univ_succ, twoDipoleConfiguration]
  ring

def twoDipoleComplexMomentCrossVelocity (coefficient : ℝ)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : ℂ :=
  (dipoleCrossCenterVelocity coefficient secondCenter firstCenter secondSeparation firstSeparation -
    dipoleCrossCenterVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation) *
      (firstSeparation - secondSeparation) +
  (firstCenter - secondCenter) *
    (dipoleCrossRelativeVelocity coefficient secondCenter firstCenter secondSeparation firstSeparation -
      dipoleCrossRelativeVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation)

theorem twoDipole_centered_complex_moment_hasDerivAt
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ} {coefficient time : ℝ}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target) time) :
    HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current)))
      ((dipoleSelfVelocity coefficient (firstSeparation time) - dipoleSelfVelocity coefficient (secondSeparation time)) *
          (firstSeparation time - secondSeparation time) +
        twoDipoleComplexMomentCrossVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) time := by
  have centerDerivative := twoDipole_centers_actual_equation equation
  have firstDerivative := (twoDipole_first_pair_equations equation).2
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
        (firstSeparation time) (secondSeparation time)) time := by
    convert secondDerivative using 1 <;> simp [dipoleCrossRelativeVelocity]
  have derivative := centerDerivative.mul (firstDerivative.sub secondDerivative')
  simp only [twoDipole_centered_complex_moment]
  convert derivative using 1
  dsimp [twoDipoleCenterRelativeVelocity, twoDipoleComplexMomentCrossVelocity]
  ring

theorem twoDipoleComplexMomentCrossVelocity_bound (coefficient : ℝ)
    {firstCenter secondCenter firstSeparation secondSeparation : ℂ} {length : ℝ}
    (lengthPositive : 0 < length)
    (firstBound : ‖firstSeparation‖ ≤ 2 * length) (secondBound : ‖secondSeparation‖ ≤ 2 * length)
    (distanceLarge : 4 * length ≤ ‖firstCenter - secondCenter‖) :
    ‖twoDipoleComplexMomentCrossVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      320 * |coefficient| * length ^ 2 / ‖firstCenter - secondCenter‖ ^ 2 := by
  let distance := ‖firstCenter - secondCenter‖
  have distancePositive : 0 < distance := lt_of_lt_of_le (by positivity) distanceLarge
  have separationBound : ‖firstSeparation‖ + ‖secondSeparation‖ ≤ distance := by
    dsimp [distance]
    linarith
  have firstCenterControl := dipoleCrossCenterVelocity_bound coefficient distancePositive
    (show ‖secondSeparation‖ + ‖firstSeparation‖ ≤ ‖firstCenter - secondCenter‖ by linarith)
  have secondCenterControl := dipoleCrossCenterVelocity_bound coefficient
    (show 0 < ‖secondCenter - firstCenter‖ by simpa only [norm_sub_rev] using distancePositive)
    (show ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖secondCenter - firstCenter‖ by
      simpa only [norm_sub_rev] using separationBound)
  have firstRelativeControl := dipoleCrossRelativeVelocity_bound coefficient distancePositive
    (show ‖secondSeparation‖ + ‖firstSeparation‖ ≤ ‖firstCenter - secondCenter‖ by linarith)
  have secondRelativeControl := dipoleCrossRelativeVelocity_bound coefficient
    (show 0 < ‖secondCenter - firstCenter‖ by simpa only [norm_sub_rev] using distancePositive)
    (show ‖firstSeparation‖ + ‖secondSeparation‖ ≤ ‖secondCenter - firstCenter‖ by
      simpa only [norm_sub_rev] using separationBound)
  rw [norm_sub_rev secondCenter firstCenter] at secondCenterControl secondRelativeControl
  have centerDifference : ‖dipoleCrossCenterVelocity coefficient secondCenter firstCenter secondSeparation firstSeparation -
      dipoleCrossCenterVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      16 * |coefficient| * length / distance ^ 2 := by
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ 4 * |coefficient| * ‖secondSeparation‖ / distance ^ 2 +
          4 * |coefficient| * ‖firstSeparation‖ / distance ^ 2 := add_le_add firstCenterControl secondCenterControl
      _ ≤ 4 * |coefficient| * (2 * length) / distance ^ 2 +
          4 * |coefficient| * (2 * length) / distance ^ 2 := by gcongr
      _ = _ := by ring
  have relativeDifference : ‖dipoleCrossRelativeVelocity coefficient secondCenter firstCenter secondSeparation firstSeparation -
      dipoleCrossRelativeVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation‖ ≤
      256 * |coefficient| * length ^ 2 / distance ^ 3 := by
    apply (norm_sub_le _ _).trans
    calc
      _ ≤ 32 * |coefficient| * ‖secondSeparation‖ * ‖firstSeparation‖ / distance ^ 3 +
          32 * |coefficient| * ‖firstSeparation‖ * ‖secondSeparation‖ / distance ^ 3 :=
        add_le_add firstRelativeControl secondRelativeControl
      _ ≤ 32 * |coefficient| * (2 * length) * (2 * length) / distance ^ 3 +
          32 * |coefficient| * (2 * length) * (2 * length) / distance ^ 3 := by gcongr
      _ = _ := by ring
  have separationDifference : ‖firstSeparation - secondSeparation‖ ≤ 4 * length :=
    (norm_sub_le _ _).trans (by linarith)
  unfold twoDipoleComplexMomentCrossVelocity
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (16 * |coefficient| * length / distance ^ 2) * (4 * length) +
        distance * (256 * |coefficient| * length ^ 2 / distance ^ 3) :=
      add_le_add (mul_le_mul centerDifference separationDifference (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left relativeDifference distancePositive.le)
    _ = _ := by
      change _ = 320 * |coefficient| * length ^ 2 / distance ^ 2
      field_simp [distancePositive.ne']
      ring

theorem twoDipole_complex_moment_self_error (frequency length : ℝ)
    {direction firstSeparation secondSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstLower : length / 2 ≤ ‖firstSeparation‖) (secondLower : length / 2 ≤ ‖secondSeparation‖)
    (firstUpper : ‖firstSeparation‖ ≤ 2 * length) (secondUpper : ‖secondSeparation‖ ≤ 2 * length) :
    ‖(dipoleSelfVelocity (frequency * length ^ 2) firstSeparation -
        dipoleSelfVelocity (frequency * length ^ 2) secondSeparation) * (firstSeparation - secondSeparation) -
      (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2)‖ ≤
      10 * frequency * length * (‖firstSeparation - (length : ℂ) * direction‖ +
        ‖secondSeparation - (length : ℂ) * (-direction)‖) := by
  let idealVelocity := -Complex.I * (frequency : ℂ) * (length : ℂ) * direction
  let idealSeparation := (length : ℂ) * direction
  let error := ‖firstSeparation - idealSeparation‖ + ‖secondSeparation - -idealSeparation‖
  have firstControl := dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive directionNorm firstLower
  have secondControl := dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive
    (show ‖-direction‖ = 1 by simpa only [norm_neg] using directionNorm) secondLower
  have negativeVelocity : -Complex.I * (frequency : ℂ) * (length : ℂ) * (-direction) = -idealVelocity := by
    dsimp [idealVelocity]
    ring
  rw [negativeVelocity] at secondControl
  have velocityError : ‖dipoleSelfVelocity (frequency * length ^ 2) firstSeparation -
      dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - 2 * idealVelocity‖ ≤ 2 * frequency * error := by
    have identity : dipoleSelfVelocity (frequency * length ^ 2) firstSeparation -
        dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - 2 * idealVelocity =
        (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - idealVelocity) -
          (dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - -idealVelocity) := by ring
    rw [identity]
    apply (norm_sub_le _ _).trans
    dsimp [error, idealSeparation]
    simpa only [mul_neg, mul_add] using add_le_add firstControl secondControl
  have separationError : ‖firstSeparation - secondSeparation - 2 * idealSeparation‖ ≤ error := by
    have identity : firstSeparation - secondSeparation - 2 * idealSeparation =
        (firstSeparation - idealSeparation) - (secondSeparation - -idealSeparation) := by ring
    rw [identity]
    exact norm_sub_le _ _
  have separationBound : ‖firstSeparation - secondSeparation‖ ≤ 4 * length :=
    (norm_sub_le _ _).trans (by linarith)
  have idealVelocityNorm : ‖2 * idealVelocity‖ = 2 * frequency * length := by
    simp [idealVelocity, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive,
      abs_of_pos lengthPositive, directionNorm]
    ring
  have idealIdentity : (2 * idealVelocity) * (2 * idealSeparation) =
      -4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2 := by
    dsimp [idealVelocity, idealSeparation]
    ring
  have productIdentity : (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation -
      dipoleSelfVelocity (frequency * length ^ 2) secondSeparation) * (firstSeparation - secondSeparation) -
      (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2) =
      (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation -
        dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - 2 * idealVelocity) *
          (firstSeparation - secondSeparation) +
        (2 * idealVelocity) * (firstSeparation - secondSeparation - 2 * idealSeparation) := by
    rw [← idealIdentity]
    ring
  rw [productIdentity]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul, idealVelocityNorm]
  have errorNonnegative : 0 ≤ error := by dsimp [error]; positivity
  calc
    _ ≤ (2 * frequency * error) * (4 * length) + (2 * frequency * length) * error :=
      add_le_add (mul_le_mul velocityError separationBound (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_left separationError (by positivity))
    _ = _ := by dsimp [error, idealSeparation]; rw [mul_neg]; ring

theorem twoDipole_centered_complex_moment_ramp
    {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {frequency length time : ℝ} {direction : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstLower : length / 2 ≤ ‖firstSeparation time‖) (secondLower : length / 2 ≤ ‖secondSeparation time‖)
    (firstUpper : ‖firstSeparation time‖ ≤ 2 * length) (secondUpper : ‖secondSeparation time‖ ≤ 2 * length)
    (distanceLarge : 4 * length ≤ ‖firstCenter time - secondCenter time‖)
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField (frequency * length ^ 2) (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target) time) :
    ∃ velocity : ℂ, HasDerivAt (fun current => fourPointCenteredComplexMoment
      (twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current))) velocity time ∧
      ‖velocity - (-4 * Complex.I * (frequency : ℂ) * (length : ℂ) ^ 2 * direction ^ 2)‖ ≤
        10 * frequency * length * (‖firstSeparation time - (length : ℂ) * direction‖ +
          ‖secondSeparation time - (length : ℂ) * (-direction)‖) +
        320 * frequency * length ^ 4 / ‖firstCenter time - secondCenter time‖ ^ 2 := by
  have derivative := twoDipole_centered_complex_moment_hasDerivAt equation
  refine ⟨_, derivative, ?_⟩
  have selfControl := twoDipole_complex_moment_self_error frequency length frequencyPositive lengthPositive
    directionNorm firstLower secondLower firstUpper secondUpper
  have crossControl := twoDipoleComplexMomentCrossVelocity_bound (frequency * length ^ 2)
    lengthPositive firstUpper secondUpper distanceLarge
  rw [abs_of_pos (by positivity : 0 < frequency * length ^ 2)] at crossControl
  have rearrange (self cross ideal : ℂ) : self + cross - ideal = (self - ideal) + cross := by ring
  rw [rearrange]
  apply (norm_add_le _ _).trans
  convert add_le_add selfControl crossControl using 1 <;> ring

end EulerNonuniqueness.Section6
