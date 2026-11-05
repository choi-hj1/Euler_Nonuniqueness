import EulerNonuniqueness.Section6.TwoDipoleDynamics

noncomputable section

namespace EulerNonuniqueness.Section6

def dipoleSelfVelocity (coefficient : ℝ) (separation : ℂ) : ℂ :=
  -Complex.I * (coefficient : ℂ) / star separation

theorem dipoleSelfVelocity_difference_norm (coefficient : ℝ) {first second : ℂ}
    (firstNonzero : first ≠ 0) (secondNonzero : second ≠ 0) :
    ‖dipoleSelfVelocity coefficient first - dipoleSelfVelocity coefficient second‖ =
      |coefficient| * ‖first - second‖ / (‖first‖ * ‖second‖) := by
  have identity : dipoleSelfVelocity coefficient first - dipoleSelfVelocity coefficient second =
      (-Complex.I * (coefficient : ℂ)) * ((star first)⁻¹ - (star second)⁻¹) := by
    dsimp [dipoleSelfVelocity]
    ring
  rw [identity, inv_sub_inv (star_ne_zero.mpr firstNonzero) (star_ne_zero.mpr secondNonzero),
    ← star_sub]
  simp [norm_mul, norm_div, norm_star, Complex.norm_real, norm_sub_rev]
  simp only [← Complex.star_def]
  rw [← star_sub, norm_star]
  ring

theorem dipoleSelfVelocity_ideal (frequency length : ℝ) {direction : ℂ}
    (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1) :
    dipoleSelfVelocity (frequency * length ^ 2) ((length : ℂ) * direction) =
      -Complex.I * (frequency : ℂ) * (length : ℂ) * direction := by
  have directionNonzero : direction ≠ 0 := norm_ne_zero_iff.mp (by rw [directionNorm]; norm_num)
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have inverse : (star direction)⁻¹ = direction :=
    (mul_eq_one_iff_inv_eq₀ (star_ne_zero.mpr directionNonzero)).mp unitProduct
  have starLength : star (length : ℂ) = (length : ℂ) := by simp [Complex.star_def]
  simp only [dipoleSelfVelocity, star_mul, starLength, div_eq_mul_inv, mul_inv_rev, inverse]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr lengthPositive.ne']
  ring

theorem dipoleSelfVelocity_ideal_error (frequency length : ℝ) {direction separation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (separationLower : length / 2 ≤ ‖separation‖) :
    ‖dipoleSelfVelocity (frequency * length ^ 2) separation -
        (-Complex.I * (frequency : ℂ) * (length : ℂ) * direction)‖ ≤
      2 * frequency * ‖separation - (length : ℂ) * direction‖ := by
  have separationPositive : 0 < ‖separation‖ := lt_of_lt_of_le (by positivity) separationLower
  have idealNorm : ‖(length : ℂ) * direction‖ = length := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, directionNorm, mul_one]
  rw [← dipoleSelfVelocity_ideal frequency length lengthPositive directionNorm,
    dipoleSelfVelocity_difference_norm (frequency * length ^ 2)
      (norm_pos_iff.mp separationPositive) (norm_ne_zero_iff.mp (by rw [idealNorm]; exact lengthPositive.ne')),
    idealNorm, abs_of_pos (by positivity : 0 < frequency * length ^ 2)]
  have denominatorBound : length ^ 2 / 2 ≤ ‖separation‖ * length := by nlinarith
  calc
    _ ≤ (frequency * length ^ 2 * ‖separation - (length : ℂ) * direction‖) / (length ^ 2 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) denominatorBound
    _ = _ := by field_simp; ring

theorem dipole_separation_norm_bounds (length : ℝ) {direction separation : ℂ}
    (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (errorBound : ‖separation - (length : ℂ) * direction‖ ≤ length / 16) :
    length / 2 ≤ ‖separation‖ ∧ ‖separation‖ ≤ 2 * length := by
  have idealNorm : ‖(length : ℂ) * direction‖ = length := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos lengthPositive, directionNorm, mul_one]
  have lower := norm_add_le ((length : ℂ) * direction - separation) separation
  rw [sub_add_cancel, idealNorm, norm_sub_rev] at lower
  have upper := norm_add_le (separation - (length : ℂ) * direction) ((length : ℂ) * direction)
  rw [sub_add_cancel, idealNorm] at upper
  constructor <;> linarith

theorem dipoleCrossCenterVelocity_small (frequency length : ℝ)
    {sourceCenter targetCenter sourceSeparation targetSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length)
    (sourceBound : ‖sourceSeparation‖ ≤ 2 * length) (targetBound : ‖targetSeparation‖ ≤ 2 * length)
    (distanceBound : 16 * length ≤ ‖targetCenter - sourceCenter‖) :
    ‖dipoleCrossCenterVelocity (frequency * length ^ 2) sourceCenter targetCenter sourceSeparation targetSeparation‖ ≤
      frequency * length / 32 := by
  have distancePositive : 0 < ‖targetCenter - sourceCenter‖ := lt_of_lt_of_le (by positivity) distanceBound
  have separationBound : ‖sourceSeparation‖ + ‖targetSeparation‖ ≤ ‖targetCenter - sourceCenter‖ := by linarith
  have control := dipoleCrossCenterVelocity_bound (frequency * length ^ 2) distancePositive separationBound
  rw [abs_of_pos (by positivity : 0 < frequency * length ^ 2)] at control
  have denominatorBound : 256 * length ^ 2 ≤ ‖targetCenter - sourceCenter‖ ^ 2 := by nlinarith
  calc
    _ ≤ 4 * (frequency * length ^ 2) * ‖sourceSeparation‖ / ‖targetCenter - sourceCenter‖ ^ 2 := control
    _ ≤ 4 * (frequency * length ^ 2) * (2 * length) / ‖targetCenter - sourceCenter‖ ^ 2 := by gcongr
    _ = 8 * frequency * length ^ 3 / ‖targetCenter - sourceCenter‖ ^ 2 := by ring
    _ ≤ 8 * frequency * length ^ 3 / (256 * length ^ 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) denominatorBound
    _ = _ := by field_simp; ring

def twoDipoleCenterRelativeVelocity (coefficient : ℝ)
    (firstCenter secondCenter firstSeparation secondSeparation : ℂ) : ℂ :=
  dipoleSelfVelocity coefficient firstSeparation - dipoleSelfVelocity coefficient secondSeparation +
    dipoleCrossCenterVelocity coefficient secondCenter firstCenter secondSeparation firstSeparation -
    dipoleCrossCenterVelocity coefficient firstCenter secondCenter firstSeparation secondSeparation

theorem twoDipoleCenterRelativeVelocity_ideal_error (frequency length : ℝ)
    {direction firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstError : ‖firstSeparation - (length : ℂ) * direction‖ ≤ length / 16)
    (secondError : ‖secondSeparation - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (distanceBound : 16 * length ≤ ‖firstCenter - secondCenter‖) :
    ‖twoDipoleCenterRelativeVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation -
        (-2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction)‖ ≤ frequency * length / 2 := by
  have negativeNorm : ‖-direction‖ = 1 := by simpa using directionNorm
  obtain ⟨firstLower, firstUpper⟩ := dipole_separation_norm_bounds length lengthPositive directionNorm firstError
  obtain ⟨secondLower, secondUpper⟩ := dipole_separation_norm_bounds length lengthPositive negativeNorm secondError
  let ideal := -Complex.I * (frequency : ℂ) * (length : ℂ) * direction
  have firstControl : ‖dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal‖ ≤ frequency * length / 8 := by
    exact (dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive directionNorm firstLower).trans (by nlinarith)
  have secondControl : ‖dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal)‖ ≤ frequency * length / 8 := by
    have control := dipoleSelfVelocity_ideal_error frequency length frequencyPositive lengthPositive negativeNorm secondLower
    have identity : -Complex.I * (frequency : ℂ) * (length : ℂ) * (-direction) = -ideal := by dsimp [ideal]; ring
    rw [identity] at control
    exact control.trans (by nlinarith)
  have firstCross := dipoleCrossCenterVelocity_small frequency length frequencyPositive lengthPositive secondUpper firstUpper distanceBound
  have secondCross := dipoleCrossCenterVelocity_small frequency length frequencyPositive lengthPositive firstUpper secondUpper
    (by simpa only [norm_sub_rev] using distanceBound)
  have identity : twoDipoleCenterRelativeVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation -
      (-2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction) =
      (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal) -
        (dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal)) +
        dipoleCrossCenterVelocity (frequency * length ^ 2) secondCenter firstCenter secondSeparation firstSeparation -
        dipoleCrossCenterVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation := by
    dsimp [twoDipoleCenterRelativeVelocity, ideal]
    ring
  rw [identity]
  have triangle := (norm_sub_le
    ((dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal) -
      (dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal)) +
      dipoleCrossCenterVelocity (frequency * length ^ 2) secondCenter firstCenter secondSeparation firstSeparation)
    (dipoleCrossCenterVelocity (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation)).trans
      (add_le_add_right (norm_add_le _ _) _)
  have selfTriangle := norm_sub_le (dipoleSelfVelocity (frequency * length ^ 2) firstSeparation - ideal)
    (dipoleSelfVelocity (frequency * length ^ 2) secondSeparation - (-ideal))
  nlinarith

theorem twoDipoleCenterRelativeVelocity_outward (frequency length : ℝ)
    {direction firstCenter secondCenter firstSeparation secondSeparation : ℂ}
    (frequencyPositive : 0 < frequency) (lengthPositive : 0 < length) (directionNorm : ‖direction‖ = 1)
    (firstError : ‖firstSeparation - (length : ℂ) * direction‖ ≤ length / 16)
    (secondError : ‖secondSeparation - (length : ℂ) * (-direction)‖ ≤ length / 16)
    (distanceBound : 16 * length ≤ ‖firstCenter - secondCenter‖) :
    frequency * length ≤ (Complex.I * star direction * twoDipoleCenterRelativeVelocity
        (frequency * length ^ 2) firstCenter secondCenter firstSeparation secondSeparation).re ∧
      ‖twoDipoleCenterRelativeVelocity (frequency * length ^ 2)
        firstCenter secondCenter firstSeparation secondSeparation‖ ≤ 3 * frequency * length := by
  let velocity := twoDipoleCenterRelativeVelocity (frequency * length ^ 2)
    firstCenter secondCenter firstSeparation secondSeparation
  let ideal := -2 * Complex.I * (frequency : ℂ) * (length : ℂ) * direction
  have errorControl : ‖velocity - ideal‖ ≤ frequency * length / 2 :=
    twoDipoleCenterRelativeVelocity_ideal_error frequency length frequencyPositive lengthPositive directionNorm
      firstError secondError distanceBound
  have unitProduct : star direction * direction = 1 := by
    simpa only [Complex.star_def, Complex.normSq_eq_norm_sq, directionNorm, one_pow, Complex.ofReal_one] using
      (Complex.normSq_eq_conj_mul_self (z := direction)).symm
  have idealProjection : Complex.I * star direction * ideal = ((2 * frequency * length : ℝ) : ℂ) := by
    calc
      _ = (-2 * (Complex.I * Complex.I) * (frequency : ℂ) * (length : ℂ)) * (star direction * direction) := by
        dsimp [ideal]
        ring
      _ = _ := by rw [Complex.I_mul_I, unitProduct]; push_cast; ring
  have projectionError : |(Complex.I * star direction * velocity).re - 2 * frequency * length| ≤
      frequency * length / 2 := by
    have realProjection := congrArg Complex.re idealProjection
    simp only [Complex.ofReal_re] at realProjection
    rw [← realProjection, ← Complex.sub_re, ← mul_sub]
    apply (Complex.abs_re_le_norm _).trans
    simpa only [norm_mul, Complex.norm_I, norm_star, directionNorm, one_mul] using errorControl
  have idealNorm : ‖ideal‖ = 2 * frequency * length := by
    simp [ideal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos frequencyPositive,
      abs_of_pos lengthPositive, directionNorm]
  have triangle := norm_add_le (velocity - ideal) ideal
  rw [sub_add_cancel, idealNorm] at triangle
  constructor
  · have lower := (abs_le.mp projectionError).1
    nlinarith
  · nlinarith

theorem twoDipole_centers_actual_equation {firstCenter secondCenter firstSeparation secondSeparation : ℝ → ℂ}
    {coefficient time : ℝ}
    (equation : ∀ target, HasDerivAt
      (fun current => twoDipoleConfiguration (firstCenter current) (secondCenter current)
        (firstSeparation current) (secondSeparation current) target)
      (fourPointField coefficient (twoDipoleConfiguration (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) target) time) :
    HasDerivAt (fun current => firstCenter current - secondCenter current)
      (twoDipoleCenterRelativeVelocity coefficient (firstCenter time) (secondCenter time)
        (firstSeparation time) (secondSeparation time)) time := by
  have firstDerivative := (twoDipole_first_pair_equations equation).1
  have positiveEquation := equation 1
  have negativeEquation := equation 3
  rw [fourPointField_twoDipoles] at positiveEquation negativeEquation
  simp only [twoDipoleConfiguration, Matrix.cons_val_zero, Matrix.cons_val_succ] at positiveEquation negativeEquation
  have secondDerivative : HasDerivAt secondCenter
      (dipoleSelfVelocity coefficient (secondSeparation time) +
        dipoleCrossCenterVelocity coefficient (firstCenter time) (secondCenter time)
          (firstSeparation time) (secondSeparation time)) time := by
    convert (positiveEquation.add negativeEquation).div_const 2 using 1
    · funext current
      dsimp
      ring
    · dsimp [dipoleSelfVelocity, dipoleCrossCenterVelocity]
      ring
  convert firstDerivative.sub secondDerivative using 1
  dsimp [twoDipoleCenterRelativeVelocity, dipoleSelfVelocity]
  ring

end EulerNonuniqueness.Section6
