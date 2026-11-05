import EulerNonuniqueness.Section6.StrainShapeForcing

noncomputable section

namespace EulerNonuniqueness.Section6

open EulerNonuniqueness.Section2

def quadrupoleCauchyField (first second position : ℂ) : ℂ :=
  1 / (position - first) + 1 / (position + first) -
    1 / (position - second) - 1 / (position + second)

def quadrupoleCauchyStrain (first second position : ℂ) : ℂ :=
  -(1 / (position - first) ^ 2) - 1 / (position + first) ^ 2 +
    1 / (position - second) ^ 2 + 1 / (position + second) ^ 2

theorem quadrupoleCauchyField_hasDerivAt (first second position : ℂ)
    (firstDifference : position - first ≠ 0) (firstSum : position + first ≠ 0)
    (secondDifference : position - second ≠ 0) (secondSum : position + second ≠ 0) :
    HasDerivAt (quadrupoleCauchyField first second) (quadrupoleCauchyStrain first second position) position := by
  have firstMinus := (hasDerivAt_const position (1 : ℂ)).div
    ((hasDerivAt_id position).sub_const first) firstDifference
  have firstPlus := (hasDerivAt_const position (1 : ℂ)).div
    ((hasDerivAt_id position).add_const first) firstSum
  have secondMinus := (hasDerivAt_const position (1 : ℂ)).div
    ((hasDerivAt_id position).sub_const second) secondDifference
  have secondPlus := (hasDerivAt_const position (1 : ℂ)).div
    ((hasDerivAt_id position).add_const second) secondSum
  convert ((firstMinus.add firstPlus).sub secondMinus).sub secondPlus using 1
  dsimp [quadrupoleCauchyStrain]
  ring

def quadrupoleStrainFactor (first second : ℂ) : ℂ :=
  -6 / ((1 - first) * (1 - second)) -
    4 * first / ((1 - first) ^ 2 * (1 - second)) -
    4 * second / ((1 - first) * (1 - second) ^ 2)

theorem normalized_quadrupole_denominator {source position : ℂ}
    (positionNonzero : position ≠ 0) :
    1 - (source / position) ^ 2 = (position - source) * (position + source) / position ^ 2 := by
  field_simp
  ring

theorem quadrupoleCauchyStrain_at_one (first second : ℂ)
    (firstDifference : 1 - first ≠ 0) (firstSum : 1 + first ≠ 0)
    (secondDifference : 1 - second ≠ 0) (secondSum : 1 + second ≠ 0) :
    quadrupoleCauchyStrain first second 1 =
      (first ^ 2 - second ^ 2) * quadrupoleStrainFactor (first ^ 2) (second ^ 2) := by
  have firstSquares : 1 - first ^ 2 = (1 - first) * (1 + first) := by ring
  have secondSquares : 1 - second ^ 2 = (1 - second) * (1 + second) := by ring
  unfold quadrupoleCauchyStrain quadrupoleStrainFactor
  rw [firstSquares, secondSquares]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
  field_simp [mul_ne_zero_iff, pow_ne_zero_iff, firstDifference, firstSum, secondDifference, secondSum]
  ring

theorem quadrupoleCauchyStrain_normalized (first second position : ℂ)
    (positionNonzero : position ≠ 0)
    (firstDifference : position - first ≠ 0) (firstSum : position + first ≠ 0)
    (secondDifference : position - second ≠ 0) (secondSum : position + second ≠ 0) :
    quadrupoleCauchyStrain first second position =
      (first ^ 2 - second ^ 2) / position ^ 4 *
        quadrupoleStrainFactor ((first / position) ^ 2) ((second / position) ^ 2) := by
  have firstMinus : 1 - first / position = (position - first) / position := by field_simp
  have firstPlus : 1 + first / position = (position + first) / position := by field_simp
  have secondMinus : 1 - second / position = (position - second) / position := by field_simp
  have secondPlus : 1 + second / position = (position + second) / position := by field_simp
  have normalized := quadrupoleCauchyStrain_at_one (first / position) (second / position)
    (by rw [firstMinus]; exact div_ne_zero firstDifference positionNonzero)
    (by rw [firstPlus]; exact div_ne_zero firstSum positionNonzero)
    (by rw [secondMinus]; exact div_ne_zero secondDifference positionNonzero)
    (by rw [secondPlus]; exact div_ne_zero secondSum positionNonzero)
  have scaling : quadrupoleCauchyStrain first second position =
      quadrupoleCauchyStrain (first / position) (second / position) 1 / position ^ 2 := by
    unfold quadrupoleCauchyStrain
    rw [firstMinus, firstPlus, secondMinus, secondPlus]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    field_simp [mul_ne_zero_iff, pow_ne_zero_iff, positionNonzero, firstDifference, firstSum, secondDifference, secondSum]
    ring
  rw [scaling, normalized]
  generalize quadrupoleStrainFactor ((first / position) ^ 2) ((second / position) ^ 2) = factor
  simp only [div_pow, div_eq_mul_inv, inv_pow]
  ring

theorem norm_inv_one_sub_le_two {point : ℂ} (small : ‖point‖ ≤ 1 / 2) :
    ‖(1 - point)⁻¹‖ ≤ 2 := by
  have reverse := norm_sub_norm_le (1 : ℂ) point
  simp only [norm_one] at reverse
  have lower : (1 / 2 : ℝ) ≤ ‖1 - point‖ := by linarith
  rw [norm_inv]
  simpa using
    one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) lower

theorem quadrupoleStrainFactor_error {first second : ℂ}
    (firstSmall : ‖first‖ ≤ 1 / 4) (secondSmall : ‖second‖ ≤ 1 / 4) :
    ‖quadrupoleStrainFactor first second + 6‖ ≤ 80 * (‖first‖ + ‖second‖) := by
  have firstInverse := norm_inv_one_sub_le_two (point := first) (by linarith)
  have secondInverse := norm_inv_one_sub_le_two (point := second) (by linarith)
  have firstNonzero : 1 - first ≠ 0 := by
    intro zero
    have : first = 1 := by linear_combination -zero
    norm_num [this] at firstSmall
  have secondNonzero : 1 - second ≠ 0 := by
    intro zero
    have : second = 1 := by linear_combination -zero
    norm_num [this] at secondSmall
  have identity : quadrupoleStrainFactor first second + 6 =
      6 * (first * second - first - second) * (1 - first)⁻¹ * (1 - second)⁻¹ -
      4 * first * ((1 - first)⁻¹) ^ 2 * (1 - second)⁻¹ -
      4 * second * (1 - first)⁻¹ * ((1 - second)⁻¹) ^ 2 := by
    unfold quadrupoleStrainFactor
    field_simp [mul_ne_zero_iff, pow_ne_zero_iff, firstNonzero, secondNonzero]
    ring
  have numeratorBound : ‖first * second - first - second‖ ≤ 2 * (‖first‖ + ‖second‖) := by
    calc
      _ ≤ ‖first * second - first‖ + ‖second‖ := norm_sub_le _ _
      _ ≤ (‖first * second‖ + ‖first‖) + ‖second‖ := add_le_add_right (norm_sub_le _ _) _
      _ = ‖first‖ * ‖second‖ + ‖first‖ + ‖second‖ := by rw [norm_mul]
      _ ≤ 2 * (‖first‖ + ‖second‖) := by nlinarith [norm_nonneg first, norm_nonneg second]
  rw [identity]
  calc
    _ ≤ ‖6 * (first * second - first - second) * (1 - first)⁻¹ * (1 - second)⁻¹ -
        4 * first * ((1 - first)⁻¹) ^ 2 * (1 - second)⁻¹‖ +
        ‖4 * second * (1 - first)⁻¹ * ((1 - second)⁻¹) ^ 2‖ := norm_sub_le _ _
    _ ≤ (‖6 * (first * second - first - second) * (1 - first)⁻¹ * (1 - second)⁻¹‖ +
        ‖4 * first * ((1 - first)⁻¹) ^ 2 * (1 - second)⁻¹‖) +
        ‖4 * second * (1 - first)⁻¹ * ((1 - second)⁻¹) ^ 2‖ :=
      add_le_add_right (norm_sub_le _ _) _
    _ = 6 * ‖first * second - first - second‖ * ‖(1 - first)⁻¹‖ * ‖(1 - second)⁻¹‖ +
        4 * ‖first‖ * ‖(1 - first)⁻¹‖ ^ 2 * ‖(1 - second)⁻¹‖ +
        4 * ‖second‖ * ‖(1 - first)⁻¹‖ * ‖(1 - second)⁻¹‖ ^ 2 := by
      simp only [norm_mul, norm_pow]
      norm_num
    _ ≤ 6 * (2 * (‖first‖ + ‖second‖)) * 2 * 2 +
        4 * ‖first‖ * 2 ^ 2 * 2 + 4 * ‖second‖ * 2 * 2 ^ 2 := by
      gcongr
    _ = 80 * (‖first‖ + ‖second‖) := by ring

theorem quadrupole_far_field_noncollision {source position : ℂ} (positionNonzero : position ≠ 0)
    (small : ‖source‖ ≤ ‖position‖ / 2) : position - source ≠ 0 ∧ position + source ≠ 0 := by
  have positionPositive := norm_pos_iff.mpr positionNonzero
  constructor
  · intro zero
    have equal : source = position := by linear_combination -zero
    rw [equal] at small
    linarith
  · intro zero
    have equal : source = -position := by linear_combination zero
    rw [equal, norm_neg] at small
    linarith

theorem quadrupoleCauchyStrain_error {first second position : ℂ} (positionNonzero : position ≠ 0)
    (firstSmall : ‖first‖ ≤ ‖position‖ / 2) (secondSmall : ‖second‖ ≤ ‖position‖ / 2) :
    ‖quadrupoleCauchyStrain first second position + 6 * (first ^ 2 - second ^ 2) / position ^ 4‖ ≤
      80 * ‖first ^ 2 - second ^ 2‖ * (‖first‖ ^ 2 + ‖second‖ ^ 2) / ‖position‖ ^ 6 := by
  have positionPositive := norm_pos_iff.mpr positionNonzero
  have firstCollision := quadrupole_far_field_noncollision positionNonzero firstSmall
  have secondCollision := quadrupole_far_field_noncollision positionNonzero secondSmall
  have firstRatio : ‖first / position‖ ≤ 1 / 2 := by
    rw [norm_div]
    apply (div_le_iff₀ positionPositive).mpr
    linarith
  have secondRatio : ‖second / position‖ ≤ 1 / 2 := by
    rw [norm_div]
    apply (div_le_iff₀ positionPositive).mpr
    linarith
  have factorBound := quadrupoleStrainFactor_error
    (first := (first / position) ^ 2) (second := (second / position) ^ 2)
    (by rw [norm_pow]; nlinarith [norm_nonneg (first / position)])
    (by rw [norm_pow]; nlinarith [norm_nonneg (second / position)])
  have errorIdentity : quadrupoleCauchyStrain first second position +
      6 * (first ^ 2 - second ^ 2) / position ^ 4 =
      (first ^ 2 - second ^ 2) / position ^ 4 *
        (quadrupoleStrainFactor ((first / position) ^ 2) ((second / position) ^ 2) + 6) := by
    rw [quadrupoleCauchyStrain_normalized first second position positionNonzero
      firstCollision.1 firstCollision.2 secondCollision.1 secondCollision.2]
    ring
  rw [errorIdentity, norm_mul, norm_div, norm_pow]
  calc
    _ ≤ (‖first ^ 2 - second ^ 2‖ / ‖position‖ ^ 4) *
        (80 * (‖(first / position) ^ 2‖ + ‖(second / position) ^ 2‖)) :=
      mul_le_mul_of_nonneg_left factorBound (by positivity)
    _ = _ := by
      simp only [norm_pow, norm_div]
      field_simp
      ring

def quadrupoleComplexMoment (circulation : ℝ) (first second : ℂ) : ℂ :=
  2 * (circulation : ℂ) * (first ^ 2 - second ^ 2)

def quadrupoleExternalVelocity (circulation : ℝ) (first second position : ℂ) : ℂ :=
  Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) *
    quadrupoleCauchyField (star first) (star second) (star position)

def quadrupoleExternalStrain (circulation : ℝ) (first second position : ℂ) : ℂ :=
  Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) *
    quadrupoleCauchyStrain (star first) (star second) (star position)

theorem quadrupoleExternalStrain_hasDerivAt (circulation : ℝ) {first second position : ℂ}
    (firstDifference : star position - star first ≠ 0) (firstSum : star position + star first ≠ 0)
    (secondDifference : star position - star second ≠ 0) (secondSum : star position + star second ≠ 0) :
    HasDerivAt (fun conjugatePosition => Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ) *
      quadrupoleCauchyField (star first) (star second) conjugatePosition)
      (quadrupoleExternalStrain circulation first second position) (star position) :=
  (quadrupoleCauchyField_hasDerivAt (star first) (star second) (star position)
    firstDifference firstSum secondDifference secondSum).const_mul _

theorem quadrupoleComplexMoment_norm (circulation : ℝ) (first second : ℂ) :
    ‖quadrupoleComplexMoment circulation first second‖ =
      2 * |circulation| * ‖first ^ 2 - second ^ 2‖ := by
  simp [quadrupoleComplexMoment, norm_mul, Complex.norm_real, Real.norm_eq_abs]

theorem quadrupoleExternalStrain_error (circulation : ℝ) {first second position : ℂ}
    (positionNonzero : position ≠ 0)
    (firstSmall : ‖first‖ ≤ ‖position‖ / 2) (secondSmall : ‖second‖ ≤ ‖position‖ / 2) :
    ‖quadrupoleExternalStrain circulation first second position +
        3 * Complex.I * star (quadrupoleComplexMoment circulation first second) /
          (2 * (Real.pi : ℂ) * star position ^ 4)‖ ≤
      (20 / Real.pi) * ‖quadrupoleComplexMoment circulation first second‖ *
        (‖first‖ ^ 2 + ‖second‖ ^ 2) / ‖position‖ ^ 6 := by
  have conjugateDifference : star first ^ 2 - star second ^ 2 = star (first ^ 2 - second ^ 2) := by
    simp only [star_sub, star_pow]
  have identity : quadrupoleExternalStrain circulation first second position +
      3 * Complex.I * star (quadrupoleComplexMoment circulation first second) /
        (2 * (Real.pi : ℂ) * star position ^ 4) =
      (Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ)) *
        (quadrupoleCauchyStrain (star first) (star second) (star position) +
          6 * (star first ^ 2 - star second ^ 2) / star position ^ 4) := by
    simp only [quadrupoleExternalStrain, quadrupoleComplexMoment, star_mul, star_sub, star_pow,
      Complex.star_def, map_mul, Complex.conj_ofReal, Complex.conj_ofNat]
    push_cast
    ring
  have estimate := quadrupoleCauchyStrain_error (star_ne_zero.mpr positionNonzero)
    (first := star first) (second := star second)
    (by simpa only [norm_star] using firstSmall) (by simpa only [norm_star] using secondSmall)
  rw [conjugateDifference, norm_star, norm_star, norm_star, norm_star] at estimate
  have coefficientNorm : ‖Complex.I * ((circulation / (2 * Real.pi) : ℝ) : ℂ)‖ = |circulation| / (2 * Real.pi) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [identity, norm_mul, coefficientNorm, conjugateDifference]
  calc
    _ ≤ (|circulation| / (2 * Real.pi)) *
        (80 * ‖first ^ 2 - second ^ 2‖ * (‖first‖ ^ 2 + ‖second‖ ^ 2) / ‖position‖ ^ 6) :=
      mul_le_mul_of_nonneg_left estimate (by positivity)
    _ = _ := by
      rw [quadrupoleComplexMoment_norm]
      ring

end EulerNonuniqueness.Section6
