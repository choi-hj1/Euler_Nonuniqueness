import EulerNonuniqueness.Section2.SeparatingQuadrature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

noncomputable section

namespace EulerNonuniqueness.Section2

def separatingComplexRatio (rootRatio : ℝ) : ℂ :=
  (-(rootRatio ^ 2 + 2 * rootRatio - 1) / 2 : ℝ) +
    Complex.I * (Real.sqrt ((1 - rootRatio ^ 2) * (rootRatio ^ 2 + 4 * rootRatio - 1)) / 2 : ℝ)

theorem separatingComplexRatio_normSq {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    Complex.normSq (separatingComplexRatio rootRatio) = rootRatio ^ 2 := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith
  have secondPositive : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    have productPositive := mul_pos (sub_pos.mpr aboveRhombus)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith [sqrt_two_gt_one])
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have radicalSquare := Real.sq_sqrt (mul_pos firstPositive secondPositive).le
  simp only [separatingComplexRatio, Complex.normSq_apply, Complex.add_re,
    Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero, Complex.add_im, Complex.mul_im, zero_add, one_mul]
  nlinarith [radicalSquare]

def separatingAngularVelocity (frequency rootRatio : ℝ) : ℝ :=
  -frequency * (1 - rootRatio ^ 2) * (rootRatio + 1) ^ 2 / (4 * rootRatio)

theorem separatingAngularVelocity_continuousAt {frequency rootRatio : ℝ}
    (rootPositive : 0 < rootRatio) :
    ContinuousAt (separatingAngularVelocity frequency) rootRatio := by
  unfold separatingAngularVelocity
  fun_prop (disch := positivity)

def separatingPhase (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℝ :=
  ∫ currentTime in (0 : ℝ)..time,
    separatingAngularVelocity frequency (separatingScalarOrbit frequency frequencyPositive currentTime)

theorem separatingPhase_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingPhase frequency frequencyPositive)
      (separatingAngularVelocity frequency (separatingScalarOrbit frequency frequencyPositive time)) time := by
  have continuous : Continuous (fun currentTime =>
      separatingAngularVelocity frequency (separatingScalarOrbit frequency frequencyPositive currentTime)) := by
    apply continuous_iff_continuousAt.mpr
    intro currentTime
    have bounds := separatingScalarOrbit_mem frequency frequencyPositive currentTime
    have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive currentTime := by
      linarith [bounds.1, sqrt_two_gt_one]
    exact (separatingAngularVelocity_continuousAt rootPositive).comp
      (separatingScalarOrbit_continuous frequency frequencyPositive).continuousAt
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable 0 time) continuous.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous.continuousAt

def separatingPositive (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℂ :=
  ((Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2))⁻¹ : ℝ) *
    Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))

def separatingNegative (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) : ℂ :=
  separatingPositive frequency frequencyPositive time *
    separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time)

theorem separatingComplexRatio_norm {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    ‖separatingComplexRatio rootRatio‖ = rootRatio := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have square := separatingComplexRatio_normSq aboveRhombus belowOne
  rw [Complex.normSq_eq_norm_sq] at square
  nlinarith [norm_nonneg (separatingComplexRatio rootRatio)]

theorem separatingPositive_norm (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    ‖separatingPositive frequency frequencyPositive time‖ =
      (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2))⁻¹ := by
  simp [separatingPositive, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]

theorem separatingNegative_norm (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    ‖separatingNegative frequency frequencyPositive time‖ =
      ‖separatingPositive frequency frequencyPositive time‖ *
        separatingScalarOrbit frequency frequencyPositive time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  rw [separatingNegative, norm_mul, separatingComplexRatio_norm bounds.1 bounds.2]

theorem separating_impulse (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    ‖separatingPositive frequency frequencyPositive time‖ ^ 2 -
      ‖separatingNegative frequency frequencyPositive time‖ ^ 2 = 1 := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  have radicalPositive := Real.sqrt_pos.mpr endpointPositive
  rw [separatingNegative_norm, separatingPositive_norm]
  have square := Real.sq_sqrt endpointPositive.le
  field_simp

theorem separating_positive_algebra (frequency rootRatio radical escapeRadical : ℝ)
    (rootNonzero : rootRatio ≠ 0)
    (radicalSquare : radical ^ 2 = 1 - rootRatio ^ 2)
    (escapeSquare : escapeRadical ^ 2 = rootRatio ^ 2 + 4 * rootRatio - 1) :
    let ratio : ℂ := (-(rootRatio ^ 2 + 2 * rootRatio - 1) / 2 : ℝ) +
      Complex.I * (radical * escapeRadical / 2 : ℝ)
    (((frequency / 4 * (rootRatio ^ 2 + 2 * rootRatio - 1) * escapeRadical / rootRatio : ℝ) +
      Complex.I * (-frequency * radical * (rootRatio + 1) ^ 2 / (4 * rootRatio) : ℝ)) *
      (2 * (1 - star ratio ^ 2))) =
      -Complex.I * (frequency * radical : ℝ) * (3 + star ratio ^ 2) := by
  dsimp
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;>
    field_simp [rootNonzero]
  all_goals
    try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [radicalSquare, escapeSquare,
      show radical ^ 3 = radical * (1 - rootRatio ^ 2) by rw [pow_succ, radicalSquare]; ring,
      show escapeRadical ^ 3 = escapeRadical * (rootRatio ^ 2 + 4 * rootRatio - 1) by
        rw [pow_succ, escapeSquare]; ring,
      show escapeRadical ^ 4 = (rootRatio ^ 2 + 4 * rootRatio - 1) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, escapeSquare]]
    ring

theorem separatingPositive_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingPositive frequency frequencyPositive)
      (((separatingEscapeVelocity frequency (separatingScalarOrbit frequency frequencyPositive time) : ℝ) +
        Complex.I * (separatingAngularVelocity frequency (separatingScalarOrbit frequency frequencyPositive time) *
          (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2))⁻¹ : ℝ)) *
        Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))) time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have amplitudeDerivative := (separating_escape_coordinate_derivative rootPositive bounds.2
    (separatingScalarOrbit_hasDerivAt frequency frequencyPositive time)).ofReal_comp
  have phaseDerivative := ((separatingPhase_hasDerivAt frequency frequencyPositive time).ofReal_comp.const_mul
    Complex.I).cexp
  convert amplitudeDerivative.mul phaseDerivative using 1
  push_cast
  ring

theorem separatingComplexRatio_square_ne_one {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    1 - star (separatingComplexRatio rootRatio) ^ 2 ≠ 0 := by
  intro equality
  have equalNorm := congrArg norm (sub_eq_zero.mp equality)
  simp only [norm_one, norm_pow, norm_star, separatingComplexRatio_norm aboveRhombus belowOne] at equalNorm
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  nlinarith

theorem separating_positive_coefficient {frequency rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    (separatingEscapeVelocity frequency rootRatio : ℂ) +
      Complex.I * (separatingAngularVelocity frequency rootRatio *
        (Real.sqrt (1 - rootRatio ^ 2))⁻¹ : ℝ) =
      -Complex.I * (frequency * Real.sqrt (1 - rootRatio ^ 2) : ℝ) *
        (3 + star (separatingComplexRatio rootRatio) ^ 2) /
        (2 * (1 - star (separatingComplexRatio rootRatio) ^ 2)) := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith
  have secondPositive : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    have productPositive := mul_pos (sub_pos.mpr aboveRhombus)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith [sqrt_two_gt_one])
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have radicalPositive := Real.sqrt_pos.mpr firstPositive
  have angularIdentity : separatingAngularVelocity frequency rootRatio *
      (Real.sqrt (1 - rootRatio ^ 2))⁻¹ =
      -frequency * Real.sqrt (1 - rootRatio ^ 2) * (rootRatio + 1) ^ 2 / (4 * rootRatio) := by
    unfold separatingAngularVelocity
    rw [← Real.sq_sqrt firstPositive.le]
    field_simp
    ring_nf
    rw [Real.sq_sqrt firstPositive.le]
    ring
  apply (eq_div_iff (mul_ne_zero (by norm_num)
    (separatingComplexRatio_square_ne_one aboveRhombus belowOne))).mpr
  rw [angularIdentity]
  have algebra := separating_positive_algebra frequency rootRatio
    (Real.sqrt (1 - rootRatio ^ 2)) (Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1))
    rootPositive.ne' (Real.sq_sqrt firstPositive.le) (Real.sq_sqrt secondPositive.le)
  simpa only [separatingEscapeVelocity, separatingComplexRatio,
    Real.sqrt_mul firstPositive.le] using algebra

theorem separating_positive_rotation_algebra (frequency radical rotation ratio : ℂ)
    (radicalNonzero : radical ≠ 0) (rotationNonzero : rotation ≠ 0)
    (radicalStar : star radical = radical) (rotationStar : star rotation = rotation⁻¹)
    (ratioNoncollision : 1 - star ratio ^ 2 ≠ 0) :
    (-Complex.I * frequency * radical * (3 + star ratio ^ 2) /
      (2 * (1 - star ratio ^ 2))) * rotation =
      -Complex.I * frequency * (3 * star (radical⁻¹ * rotation) ^ 2 +
        star (radical⁻¹ * rotation * ratio) ^ 2) /
        (2 * star (radical⁻¹ * rotation) *
          (star (radical⁻¹ * rotation) ^ 2 - star (radical⁻¹ * rotation * ratio) ^ 2)) := by
  simp only [star_mul, star_inv₀]
  simp only [radicalStar, rotationStar]
  rw [show (rotation⁻¹ * radical⁻¹) ^ 2 - (star ratio * (rotation⁻¹ * radical⁻¹)) ^ 2 =
    (rotation⁻¹ * radical⁻¹) ^ 2 * (1 - star ratio ^ 2) by ring]
  generalize differenceDefinition : 1 - star ratio ^ 2 = difference at *
  field_simp [radicalNonzero, rotationNonzero, ratioNoncollision, radicalStar, rotationStar]
  <;> ring

theorem separatingPositive_pointEquation (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingPositive frequency frequencyPositive)
      (-Complex.I * (frequency : ℂ) *
        (3 * star (separatingPositive frequency frequencyPositive time) ^ 2 +
          star (separatingNegative frequency frequencyPositive time) ^ 2) /
        (2 * star (separatingPositive frequency frequencyPositive time) *
          (star (separatingPositive frequency frequencyPositive time) ^ 2 -
            star (separatingNegative frequency frequencyPositive time) ^ 2))) time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have radicalPositive : 0 < Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [bounds.2])
  have rotationNorm : ‖Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have rotationStar : star (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))) =
      (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [Complex.star_def, rotationNorm] using
      Complex.conj_mul' (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))
  have derivative := separatingPositive_hasDerivAt frequency frequencyPositive time
  rw [separating_positive_coefficient bounds.1 bounds.2] at derivative
  have algebra := separating_positive_rotation_algebra (frequency : ℂ)
    (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) : ℂ)
    (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))
    (separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time))
    (by exact_mod_cast radicalPositive.ne') (Complex.exp_ne_zero _) (by simp) rotationStar
    (separatingComplexRatio_square_ne_one bounds.1 bounds.2)
  push_cast at derivative
  simp only [← mul_assoc] at derivative
  rw [algebra] at derivative
  simpa only [separatingPositive, separatingNegative, Complex.ofReal_inv] using derivative

set_option maxHeartbeats 1600000 in
theorem separating_negative_algebra (frequency rootRatio radical escapeRadical : ℝ)
    (rootNonzero : rootRatio ≠ 0)
    (radicalSquare : radical ^ 2 = 1 - rootRatio ^ 2)
    (escapeSquare : escapeRadical ^ 2 = rootRatio ^ 2 + 4 * rootRatio - 1) :
    let ratio : ℂ := (-(rootRatio ^ 2 + 2 * rootRatio - 1) / 2 : ℝ) +
      Complex.I * (radical * escapeRadical / 2 : ℝ)
    (((-frequency * (rootRatio ^ 2 + 2 * rootRatio - 1) ^ 2 * escapeRadical / (8 * rootRatio) -
        frequency * (rootRatio + 1) * radical ^ 2 * (rootRatio ^ 2 + 2 * rootRatio - 1) * escapeRadical /
          (4 * rootRatio ^ 2) + frequency * radical ^ 2 * (rootRatio + 1) ^ 2 * escapeRadical /
          (8 * rootRatio) : ℝ) +
      Complex.I * (frequency * (rootRatio + 2) * radical ^ 3 * (rootRatio ^ 2 + 2 * rootRatio - 1) /
          (8 * rootRatio ^ 2) + frequency * radical * (rootRatio + 1) ^ 2 *
          (rootRatio ^ 2 + 2 * rootRatio - 1) / (8 * rootRatio) : ℝ)) *
      (2 * star ratio * (1 - star ratio ^ 2))) =
      -Complex.I * (frequency * radical : ℝ) * (1 + 3 * star ratio ^ 2) := by
  dsimp
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.star_def, pow_two] <;>
    field_simp [rootNonzero]
  all_goals
    simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [radicalSquare, escapeSquare,
      show radical ^ 3 = radical * (1 - rootRatio ^ 2) by rw [pow_succ, radicalSquare]; ring,
      show radical ^ 4 = (1 - rootRatio ^ 2) ^ 2 by rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, radicalSquare],
      show radical ^ 5 = radical * (1 - rootRatio ^ 2) ^ 2 by
        rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, radicalSquare]; ring,
      show radical ^ 6 = (1 - rootRatio ^ 2) ^ 3 by
        rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, radicalSquare],
      show escapeRadical ^ 3 = escapeRadical * (rootRatio ^ 2 + 4 * rootRatio - 1) by
        rw [pow_succ, escapeSquare]; ring,
      show escapeRadical ^ 4 = (rootRatio ^ 2 + 4 * rootRatio - 1) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, escapeSquare]]
    ring

theorem separatingNegative_eq (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingNegative frequency frequencyPositive time =
      ((-(separatingScalarOrbit frequency frequencyPositive time ^ 2 +
          2 * separatingScalarOrbit frequency frequencyPositive time - 1) /
          (2 * Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2)) : ℝ) +
        Complex.I * (Real.sqrt (separatingScalarOrbit frequency frequencyPositive time ^ 2 +
          4 * separatingScalarOrbit frequency frequencyPositive time - 1) / 2 : ℝ)) *
        Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)) := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  have radicalPositive := Real.sqrt_pos.mpr endpointPositive
  have radicalNonzero : (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) : ℂ) ≠ 0 := by
    exact_mod_cast radicalPositive.ne'
  unfold separatingNegative separatingPositive separatingComplexRatio
  rw [Real.sqrt_mul endpointPositive.le]
  push_cast
  field_simp [radicalNonzero]
  <;> ring

def separatingNegativeCoefficient (frequency rootRatio : ℝ) : ℂ :=
  ((-separatingEscapeVelocity frequency rootRatio * (rootRatio ^ 2 + 2 * rootRatio - 1) / 2 -
    (rootRatio + 1) * separatingScalarVelocity frequency rootRatio / Real.sqrt (1 - rootRatio ^ 2) -
    separatingAngularVelocity frequency rootRatio * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) / 2 : ℝ) +
    Complex.I * ((rootRatio + 2) * separatingScalarVelocity frequency rootRatio /
      (2 * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1)) -
      separatingAngularVelocity frequency rootRatio * (rootRatio ^ 2 + 2 * rootRatio - 1) /
        (2 * Real.sqrt (1 - rootRatio ^ 2)) : ℝ))

theorem separatingNegative_hasDerivAt (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    let rootRatio := separatingScalarOrbit frequency frequencyPositive time
    let scalarVelocity := separatingScalarVelocity frequency rootRatio
    let escapeVelocity := separatingEscapeVelocity frequency rootRatio
    let angularVelocity := separatingAngularVelocity frequency rootRatio
    HasDerivAt (separatingNegative frequency frequencyPositive)
      (((-escapeVelocity * (rootRatio ^ 2 + 2 * rootRatio - 1) / 2 -
        (rootRatio + 1) * scalarVelocity / Real.sqrt (1 - rootRatio ^ 2) -
        angularVelocity * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) / 2 : ℝ) +
        Complex.I * ((rootRatio + 2) * scalarVelocity /
          (2 * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1)) -
          angularVelocity * (rootRatio ^ 2 + 2 * rootRatio - 1) /
            (2 * Real.sqrt (1 - rootRatio ^ 2)) : ℝ)) *
        Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))) time := by
  dsimp only
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  have escapePositive : 0 < separatingScalarOrbit frequency frequencyPositive time ^ 2 +
      4 * separatingScalarOrbit frequency frequencyPositive time - 1 := by
    have productPositive := mul_pos (sub_pos.mpr bounds.1)
      (show 0 < separatingScalarOrbit frequency frequencyPositive time + Real.sqrt 2 + 1 by
        linarith [sqrt_two_gt_one])
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have scalarDerivative := separatingScalarOrbit_hasDerivAt frequency frequencyPositive time
  have amplitudeDerivative := separating_escape_coordinate_derivative rootPositive bounds.2 scalarDerivative
  have realDerivative := ((amplitudeDerivative.mul
    (((scalarDerivative.pow 2).add (scalarDerivative.const_mul 2)).sub_const 1)).neg.div_const 2).ofReal_comp
  have imagDerivative := (((((scalarDerivative.pow 2).add
    (scalarDerivative.const_mul 4)).sub_const 1).sqrt escapePositive.ne').div_const 2).ofReal_comp
  have rotationDerivative := ((separatingPhase_hasDerivAt frequency frequencyPositive time).ofReal_comp.const_mul
    Complex.I).cexp
  have result := (realDerivative.add (imagDerivative.const_mul Complex.I)).mul rotationDerivative
  convert result using 1
  · funext currentTime
    rw [separatingNegative_eq]
    push_cast
    ring
  · push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring

set_option maxHeartbeats 1600000 in
theorem separating_negative_coefficient {frequency rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    separatingNegativeCoefficient frequency rootRatio =
      -Complex.I * (frequency * Real.sqrt (1 - rootRatio ^ 2) : ℝ) *
        (1 + 3 * star (separatingComplexRatio rootRatio) ^ 2) /
        (2 * star (separatingComplexRatio rootRatio) *
          (1 - star (separatingComplexRatio rootRatio) ^ 2)) := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have firstPositive : 0 < 1 - rootRatio ^ 2 := by nlinarith
  have secondPositive : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    have productPositive := mul_pos (sub_pos.mpr aboveRhombus)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith [sqrt_two_gt_one])
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have radicalPositive := Real.sqrt_pos.mpr firstPositive
  have escapePositive := Real.sqrt_pos.mpr secondPositive
  have ratioNonzero : separatingComplexRatio rootRatio ≠ 0 := by
    intro equality
    have := separatingComplexRatio_norm aboveRhombus belowOne
    rw [equality, norm_zero] at this
    linarith
  apply (eq_div_iff (mul_ne_zero
    (mul_ne_zero (by norm_num) (star_ne_zero.mpr ratioNonzero))
    (separatingComplexRatio_square_ne_one aboveRhombus belowOne))).mpr
  have algebra := separating_negative_algebra frequency rootRatio
    (Real.sqrt (1 - rootRatio ^ 2)) (Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1))
    rootPositive.ne' (Real.sq_sqrt firstPositive.le) (Real.sq_sqrt secondPositive.le)
  simp only [← Real.sqrt_mul firstPositive.le] at algebra
  change _ = _ at algebra
  convert algebra using 1
  congr 1
  unfold separatingNegativeCoefficient separatingEscapeVelocity separatingScalarVelocity separatingAngularVelocity
  have radicalSquare := Real.sq_sqrt firstPositive.le
  have escapeSquare := Real.sq_sqrt secondPositive.le
  generalize radicalDefinition : Real.sqrt (1 - rootRatio ^ 2) = radical at *
  generalize escapeDefinition : Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) = escapeRadical at *
  apply Complex.ext <;>
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, pow_two] <;>
    field_simp [rootPositive.ne', radicalPositive.ne', escapePositive.ne']
  all_goals
    try simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
    ring_nf
    simp only [radicalSquare, escapeSquare,
      show radical ^ 3 = radical * (1 - rootRatio ^ 2) by
        rw [pow_succ, radicalSquare]; ring,
      show radical ^ 4 = (1 - rootRatio ^ 2) ^ 2 by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, radicalSquare],
      show radical ^ 5 = radical * (1 - rootRatio ^ 2) ^ 2 by
        rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, radicalSquare]; ring,
      show radical ^ 7 = radical * (1 - rootRatio ^ 2) ^ 3 by
        rw [show (7 : ℕ) = 2 * 3 + 1 by norm_num, pow_succ, pow_mul, radicalSquare]; ring,
      show escapeRadical ^ 3 = escapeRadical * (rootRatio ^ 2 + 4 * rootRatio - 1) by
        rw [pow_succ, escapeSquare]; ring]
    ring

theorem separating_negative_rotation_algebra (frequency radical rotation ratio : ℂ)
    (radicalNonzero : radical ≠ 0) (rotationNonzero : rotation ≠ 0) (ratioNonzero : ratio ≠ 0)
    (radicalStar : star radical = radical) (rotationStar : star rotation = rotation⁻¹)
    (ratioNoncollision : 1 - star ratio ^ 2 ≠ 0) :
    (-Complex.I * frequency * radical * (1 + 3 * star ratio ^ 2) /
      (2 * star ratio * (1 - star ratio ^ 2))) * rotation =
      -Complex.I * frequency * (star (radical⁻¹ * rotation) ^ 2 +
        3 * star (radical⁻¹ * rotation * ratio) ^ 2) /
        (2 * star (radical⁻¹ * rotation * ratio) *
          (star (radical⁻¹ * rotation) ^ 2 - star (radical⁻¹ * rotation * ratio) ^ 2)) := by
  simp only [star_mul, star_inv₀]
  simp only [radicalStar, rotationStar]
  rw [show (rotation⁻¹ * radical⁻¹) ^ 2 - (star ratio * (rotation⁻¹ * radical⁻¹)) ^ 2 =
    (rotation⁻¹ * radical⁻¹) ^ 2 * (1 - star ratio ^ 2) by ring]
  generalize differenceDefinition : 1 - star ratio ^ 2 = difference at *
  field_simp [radicalNonzero, rotationNonzero, ratioNoncollision, radicalStar, rotationStar,
    star_ne_zero.mpr ratioNonzero]
  ring_nf
  simp only [starRingEnd_apply]
  generalize inverseRatioDefinition : (star ratio)⁻¹ = inverseRatio
  generalize inverseDifferenceDefinition : difference⁻¹ = inverseDifference
  field_simp [radicalNonzero, rotationNonzero, star_ne_zero.mpr ratioNonzero, ratioNoncollision]
  <;> ring

theorem separatingNegative_pointEquation (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    HasDerivAt (separatingNegative frequency frequencyPositive)
      (-Complex.I * (frequency : ℂ) *
        (star (separatingPositive frequency frequencyPositive time) ^ 2 +
          3 * star (separatingNegative frequency frequencyPositive time) ^ 2) /
        (2 * star (separatingNegative frequency frequencyPositive time) *
          (star (separatingPositive frequency frequencyPositive time) ^ 2 -
            star (separatingNegative frequency frequencyPositive time) ^ 2))) time := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have radicalPositive : 0 < Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) :=
    Real.sqrt_pos.mpr (by nlinarith [bounds.2])
  have ratioNonzero : separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time) ≠ 0 := by
    intro equality
    have := separatingComplexRatio_norm bounds.1 bounds.2
    rw [equality, norm_zero] at this
    linarith
  have rotationNorm : ‖Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have rotationStar : star (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))) =
      (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa [Complex.star_def, rotationNorm] using
      Complex.conj_mul' (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))
  have derivative := separatingNegative_hasDerivAt frequency frequencyPositive time
  change HasDerivAt _ (separatingNegativeCoefficient frequency
    (separatingScalarOrbit frequency frequencyPositive time) *
      Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ))) time at derivative
  rw [separating_negative_coefficient bounds.1 bounds.2] at derivative
  have algebra := separating_negative_rotation_algebra (frequency : ℂ)
    (Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) : ℂ)
    (Complex.exp (Complex.I * (separatingPhase frequency frequencyPositive time : ℂ)))
    (separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time))
    (by exact_mod_cast radicalPositive.ne') (Complex.exp_ne_zero _) ratioNonzero (by simp) rotationStar
    (separatingComplexRatio_square_ne_one bounds.1 bounds.2)
  push_cast at derivative
  simp only [← mul_assoc] at derivative
  rw [algebra] at derivative
  simpa only [separatingPositive, separatingNegative, Complex.ofReal_inv] using derivative

theorem separatingComplexRatio_continuous : Continuous separatingComplexRatio := by
  unfold separatingComplexRatio
  fun_prop

theorem separatingComplexRatio_at_one : separatingComplexRatio 1 = -1 := by
  norm_num [separatingComplexRatio]

theorem separatingComplexRatio_at_rhombus :
    separatingComplexRatio (Real.sqrt 2 - 1) = Complex.I * ((Real.sqrt 2 - 1 : ℝ) : ℂ) := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have polynomialZero : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by nlinarith
  have first : 1 - (Real.sqrt 2 - 1) ^ 2 = 2 * (Real.sqrt 2 - 1) := by nlinarith
  have second : (Real.sqrt 2 - 1) ^ 2 + 4 * (Real.sqrt 2 - 1) - 1 = 2 * (Real.sqrt 2 - 1) := by nlinarith
  unfold separatingComplexRatio
  rw [polynomialZero, first, second, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos (by norm_num) rootPositive)]
  push_cast
  ring

theorem separatingComplexRatio_im_nonneg (rootRatio : ℝ) :
    0 ≤ (separatingComplexRatio rootRatio).im := by
  simp only [separatingComplexRatio, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul,
    one_mul, zero_add]
  positivity

theorem separatingComplexRatio_pair_normSq {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    Complex.normSq (1 + separatingComplexRatio rootRatio) = 2 * (1 - rootRatio) ∧
      Complex.normSq (1 - separatingComplexRatio rootRatio) = 2 * rootRatio * (rootRatio + 1) := by
  have ratioSquare := separatingComplexRatio_normSq aboveRhombus belowOne
  constructor
  · rw [Complex.normSq_add, Complex.normSq_one, ratioSquare]
    simp only [one_mul, Complex.conj_re, separatingComplexRatio, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring
  · rw [Complex.normSq_sub, Complex.normSq_one, ratioSquare]
    simp only [one_mul, Complex.conj_re, separatingComplexRatio, Complex.add_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, add_zero]
    ring

theorem separating_pair_distance_squares (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    ‖separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time‖ ^ 2 =
      2 / (1 + separatingScalarOrbit frequency frequencyPositive time) ∧
    ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ ^ 2 =
      2 * separatingScalarOrbit frequency frequencyPositive time /
        (1 - separatingScalarOrbit frequency frequencyPositive time) := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  have square := Real.sq_sqrt endpointPositive.le
  have pairSquares := separatingComplexRatio_pair_normSq bounds.1 bounds.2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at pairSquares
  have radicalPositive := Real.sqrt_pos.mpr endpointPositive
  constructor
  · rw [separatingNegative, ← mul_one_add, norm_mul, mul_pow,
      pairSquares.1, separatingPositive_norm]
    field_simp
    nlinarith [square]
  · rw [separatingNegative, ← mul_one_sub, norm_mul, mul_pow,
      pairSquares.2, separatingPositive_norm]
    field_simp [(sub_pos.mpr bounds.2).ne']
    nlinarith [square]

theorem separatingPositive_ne_zero (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingPositive frequency frequencyPositive time ≠ 0 := by
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1, sqrt_two_gt_one]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  apply norm_ne_zero_iff.mp
  rw [separatingPositive_norm]
  exact inv_ne_zero (Real.sqrt_pos.mpr endpointPositive).ne'

theorem separating_position_ratio (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    separatingNegative frequency frequencyPositive time / separatingPositive frequency frequencyPositive time =
      separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time) := by
  rw [separatingNegative, mul_div_cancel_left₀ _ (separatingPositive_ne_zero frequency frequencyPositive time)]

theorem separating_norm_ratio (frequency : ℝ) (frequencyPositive : 0 < frequency) (time : ℝ) :
    ‖separatingNegative frequency frequencyPositive time‖ ^ 2 /
      ‖separatingPositive frequency frequencyPositive time‖ ^ 2 =
      separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
  rw [separatingNegative_norm, mul_pow, mul_div_cancel_left₀ _
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (separatingPositive_ne_zero frequency frequencyPositive time)))]

theorem separating_angle_outgoing_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => 2 * Complex.arg
      (separatingNegative frequency frequencyPositive time / separatingPositive frequency frequencyPositive time))
      Filter.atTop (nhds (2 * Real.pi)) := by
  have ratioLimit : Filter.Tendsto
      (fun time => separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time))
      Filter.atTop (nhdsWithin (-1 : ℂ) {position : ℂ | 0 ≤ position.im}) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert separatingComplexRatio_continuous.continuousAt.tendsto.comp
        (separatingScalarOrbit_outgoing_limit frequency frequencyPositive) using 1
      rw [separatingComplexRatio_at_one]
    · exact Filter.Eventually.of_forall (fun time => separatingComplexRatio_im_nonneg _)
  have angleLimit := (Complex.tendsto_arg_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (z := (-1 : ℂ)) (by norm_num) (by norm_num)).comp ratioLimit
  simpa only [separating_position_ratio] using angleLimit.const_mul 2

theorem separating_angle_incoming_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => 2 * Complex.arg
      (separatingNegative frequency frequencyPositive time / separatingPositive frequency frequencyPositive time))
      Filter.atBot (nhds Real.pi) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have ratioLimit : Filter.Tendsto
      (fun time => separatingComplexRatio (separatingScalarOrbit frequency frequencyPositive time))
      Filter.atBot (nhds (Complex.I * ((Real.sqrt 2 - 1 : ℝ) : ℂ))) := by
    convert separatingComplexRatio_continuous.continuousAt.tendsto.comp
      (separatingScalarOrbit_incoming_limit frequency frequencyPositive) using 1
    rw [separatingComplexRatio_at_rhombus]
  have angleLimit := (Complex.continuousAt_arg (x := Complex.I * ((Real.sqrt 2 - 1 : ℝ) : ℂ))
    (by apply Complex.mem_slitPlane_iff.mpr; right; simpa using rootPositive.ne')).tendsto.comp ratioLimit
  have angleValue : Complex.arg (Complex.I * ((Real.sqrt 2 - 1 : ℝ) : ℂ)) = Real.pi / 2 := by
    rw [Complex.arg_mul_real rootPositive, Complex.arg_I]
  have result := angleLimit.const_mul 2
  rw [angleValue] at result
  convert result using 1
  · funext time
    rw [separating_position_ratio]
    rfl
  · congr 1
    ring

theorem separating_radial_incoming_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => ‖separatingNegative frequency frequencyPositive time‖ ^ 2 /
      ‖separatingPositive frequency frequencyPositive time‖ ^ 2)
      Filter.atBot (nhds (3 - 2 * Real.sqrt 2)) := by
  have result := (separatingScalarOrbit_incoming_limit frequency frequencyPositive).pow 2
  have square : (Real.sqrt 2 - 1) ^ 2 = 3 - 2 * Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  simpa only [separating_norm_ratio, square] using result

theorem separating_radial_outgoing_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => ‖separatingNegative frequency frequencyPositive time‖ ^ 2 /
      ‖separatingPositive frequency frequencyPositive time‖ ^ 2)
      Filter.atTop (nhds 1) := by
  simpa only [separating_norm_ratio, one_pow] using
    (separatingScalarOrbit_outgoing_limit frequency frequencyPositive).pow 2

theorem separating_uniform_noncollision (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ distanceMin > (0 : ℝ), ∀ time,
      distanceMin ≤ 2 * ‖separatingPositive frequency frequencyPositive time‖ ∧
      distanceMin ≤ 2 * ‖separatingNegative frequency frequencyPositive time‖ ∧
      distanceMin ≤ ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ ∧
      distanceMin ≤ ‖separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time‖ := by
  have minimumPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have minimumBelowOne : Real.sqrt 2 - 1 < 1 := by linarith [sqrt_two_lt_three_halves]
  refine ⟨Real.sqrt 2 - 1, minimumPositive, ?_⟩
  intro time
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  have rootPositive : 0 < separatingScalarOrbit frequency frequencyPositive time := by
    linarith [bounds.1]
  have endpointPositive : 0 < 1 - separatingScalarOrbit frequency frequencyPositive time ^ 2 := by
    nlinarith [bounds.2]
  have radicalPositive := Real.sqrt_pos.mpr endpointPositive
  have radicalLe : Real.sqrt (1 - separatingScalarOrbit frequency frequencyPositive time ^ 2) ≤ 1 :=
    Real.sqrt_le_one.mpr (by nlinarith)
  have amplitudeLe : 1 ≤ ‖separatingPositive frequency frequencyPositive time‖ := by
    rw [separatingPositive_norm]
    have inversePositive := inv_pos.mpr radicalPositive
    have cancellation := mul_inv_cancel₀ radicalPositive.ne'
    nlinarith [mul_nonneg (sub_nonneg.mpr radicalLe) inversePositive.le]
  have negativeLe : separatingScalarOrbit frequency frequencyPositive time ≤
      ‖separatingNegative frequency frequencyPositive time‖ := by
    rw [separatingNegative_norm]
    nlinarith [mul_nonneg (sub_nonneg.mpr amplitudeLe) rootPositive.le]
  have distances := separating_pair_distance_squares frequency frequencyPositive time
  have sumSquareLe : 1 ≤ ‖separatingPositive frequency frequencyPositive time +
      separatingNegative frequency frequencyPositive time‖ ^ 2 := by
    rw [distances.1]
    apply (le_div_iff₀ (show 0 < 1 + separatingScalarOrbit frequency frequencyPositive time by linarith)).mpr
    linarith [bounds.2]
  have differenceSquareLe : 2 * separatingScalarOrbit frequency frequencyPositive time ≤
      ‖separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time‖ ^ 2 := by
    rw [distances.2]
    apply (le_div_iff₀ (sub_pos.mpr bounds.2)).mpr
    nlinarith
  refine ⟨by linarith, by linarith [bounds.1], ?_, ?_⟩
  · nlinarith [norm_nonneg (separatingPositive frequency frequencyPositive time - separatingNegative frequency frequencyPositive time), bounds.1]
  · nlinarith [norm_nonneg (separatingPositive frequency frequencyPositive time + separatingNegative frequency frequencyPositive time)]

theorem separatingAngularVelocity_at_rhombus (frequency : ℝ) :
    separatingAngularVelocity frequency (Real.sqrt 2 - 1) = -frequency := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have first : 1 - (Real.sqrt 2 - 1) ^ 2 = 2 * (Real.sqrt 2 - 1) := by nlinarith
  unfold separatingAngularVelocity
  rw [first, show Real.sqrt 2 - 1 + 1 = Real.sqrt 2 by ring, square]
  field_simp
  <;> ring

def separatingIncomingPhaseCoordinate (frequency : ℝ) (frequencyPositive : 0 < frequency) (rootRatio : ℝ) : ℝ :=
  separatingPhase frequency frequencyPositive (separatingQuadrature frequency rootRatio) +
    frequency * separatingQuadrature frequency rootRatio

theorem separatingIncomingPhaseCoordinate_hasDerivAt {frequency rootRatio : ℝ}
    (frequencyPositive : 0 < frequency) (bounds : rootRatio ∈ Set.Ioo (Real.sqrt 2 - 1) 1) :
    HasDerivAt (separatingIncomingPhaseCoordinate frequency frequencyPositive)
      ((separatingAngularVelocity frequency rootRatio + frequency) /
        separatingScalarVelocity frequency rootRatio) rootRatio := by
  have quadratureDerivative := separatingQuadrature_hasDerivAt frequencyPositive bounds.1 bounds.2
  have phaseDerivative := (separatingPhase_hasDerivAt frequency frequencyPositive
    (separatingQuadrature frequency rootRatio)).comp rootRatio quadratureDerivative
  rw [separatingScalarOrbit_quadrature frequency frequencyPositive bounds] at phaseDerivative
  convert phaseDerivative.add (quadratureDerivative.const_mul frequency) using 1
  ring

theorem separatingPhase_incoming_limit (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ phaseLimit : ℝ, Filter.Tendsto
      (fun time => separatingPhase frequency frequencyPositive time + frequency * time)
      Filter.atBot (nhds phaseLimit) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have ratePositive : 0 < 2 * Real.sqrt 2 * frequency := by positivity
  have numeratorDifferentiable : DifferentiableAt ℝ
      (fun value => separatingAngularVelocity frequency value + frequency) (Real.sqrt 2 - 1) := by
    unfold separatingAngularVelocity
    fun_prop (disch := positivity)
  obtain ⟨bound, boundPositive, localBound⟩ := removable_quotient_eventually_bounded ratePositive
    (separatingScalarLinearFactor_at_rhombus frequency)
    (separatingScalarLinearFactor_continuousAt_rhombus frequency)
    (show separatingAngularVelocity frequency (Real.sqrt 2 - 1) + frequency = 0 by
      rw [separatingAngularVelocity_at_rhombus]; ring) numeratorDifferentiable
  obtain ⟨radius, radiusPositive, radiusProperty⟩ := Metric.eventually_nhds_iff.mp localBound
  have endpointGap : 0 < 1 - (Real.sqrt 2 - 1) := by linarith [sqrt_two_lt_three_halves]
  have smallPositive : 0 < min radius (1 - (Real.sqrt 2 - 1)) := lt_min radiusPositive endpointGap
  have coordinateLimit : ∃ limit : ℝ, Filter.Tendsto
      (separatingIncomingPhaseCoordinate frequency frequencyPositive)
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1))) (nhds limit) := by
    apply exists_right_limit_of_bounded_derivative
      (right := Real.sqrt 2 - 1 + min radius (1 - (Real.sqrt 2 - 1)))
      (bound := bound) (by linarith) boundPositive.le
      (derivative := fun value => (separatingAngularVelocity frequency value + frequency) /
        separatingScalarVelocity frequency value)
    · intro value bounds
      apply separatingIncomingPhaseCoordinate_hasDerivAt frequencyPositive ⟨bounds.1, ?_⟩
      have := min_le_right radius (1 - (Real.sqrt 2 - 1))
      linarith [bounds.2]
    · intro value bounds
      rw [separatingScalarVelocity_factorization]
      apply radiusProperty _ (ne_of_gt bounds.1)
      rw [Real.dist_eq, abs_of_pos (sub_pos.mpr bounds.1)]
      have := min_le_left radius (1 - (Real.sqrt 2 - 1))
      linarith [bounds.2]
  obtain ⟨phaseLimit, phaseLimitProperty⟩ := coordinateLimit
  refine ⟨phaseLimit, ?_⟩
  have scalarWithin := tendsto_Ioo_atBot.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atBot
  have result := phaseLimitProperty.comp scalarWithin
  change Filter.Tendsto (fun time => separatingIncomingPhaseCoordinate frequency frequencyPositive
    (separatingScalarOrbit frequency frequencyPositive time)) _ _ at result
  simpa only [separatingIncomingPhaseCoordinate,
    separatingQuadrature_scalarOrbit] using result

def separatingRadialShape (rootRatio : ℝ) : ℝ :=
  (rootRatio ^ 2 - (Real.sqrt 2 - 1) ^ 2) / (Real.sqrt 2 - 1) ^ 2

def separatingAngularShape (rootRatio : ℝ) : ℝ :=
  (2 * Real.arccos (-(rootRatio ^ 2 + 2 * rootRatio - 1) / (2 * rootRatio)) - Real.pi) / Real.sqrt 2

def separatingUnstableShape (rootRatio : ℝ) : ℝ :=
  (separatingRadialShape rootRatio + separatingAngularShape rootRatio) / 2

def separatingStableShape (rootRatio : ℝ) : ℝ :=
  (separatingRadialShape rootRatio - separatingAngularShape rootRatio) / 2

theorem separating_arg_eq_arccos {rootRatio : ℝ}
    (aboveRhombus : Real.sqrt 2 - 1 < rootRatio) (belowOne : rootRatio < 1) :
    Complex.arg (separatingComplexRatio rootRatio) =
      Real.arccos (-(rootRatio ^ 2 + 2 * rootRatio - 1) / (2 * rootRatio)) := by
  have rootPositive : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have ratioNonzero : separatingComplexRatio rootRatio ≠ 0 := by
    intro equality
    have := separatingComplexRatio_norm aboveRhombus belowOne
    rw [equality, norm_zero] at this
    linarith
  rw [Complex.arg_of_im_nonneg_of_ne_zero (separatingComplexRatio_im_nonneg rootRatio) ratioNonzero,
    separatingComplexRatio_norm aboveRhombus belowOne]
  congr 1
  simp only [separatingComplexRatio, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem separatingRadialShape_hasDerivAt_rhombus :
    HasDerivAt separatingRadialShape (2 / (Real.sqrt 2 - 1)) (Real.sqrt 2 - 1) := by
  have rootNonzero : Real.sqrt 2 - 1 ≠ 0 := by linarith [sqrt_two_gt_one]
  convert ((((hasDerivAt_id (Real.sqrt 2 - 1)).pow 2).sub_const
    ((Real.sqrt 2 - 1) ^ 2)).div_const ((Real.sqrt 2 - 1) ^ 2)) using 1
  field_simp
  <;> ring

theorem separatingAngularShape_hasDerivAt_rhombus :
    HasDerivAt separatingAngularShape (2 / (Real.sqrt 2 - 1)) (Real.sqrt 2 - 1) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have sqrtPositive : 0 < Real.sqrt 2 := by positivity
  have polynomialZero : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have innerValue : -((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) /
      (2 * (Real.sqrt 2 - 1)) = 0 := by rw [polynomialZero]; simp
  have innerDerivative : HasDerivAt (fun value : ℝ => -(value ^ 2 + 2 * value - 1) / (2 * value))
      (-Real.sqrt 2 / (Real.sqrt 2 - 1)) (Real.sqrt 2 - 1) := by
    convert (((((hasDerivAt_id (Real.sqrt 2 - 1)).pow 2).add
      ((hasDerivAt_id _).const_mul 2)).sub_const 1).neg.div
        ((hasDerivAt_id _).const_mul 2) (mul_ne_zero (by norm_num) rootPositive.ne')) using 1
    simp only [id_eq, Nat.reduceSub, pow_one, mul_one]
    rw [polynomialZero]
    field_simp
    <;> ring
  have arcDerivative : HasDerivAt Real.arccos (-1)
      (-((Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1) / (2 * (Real.sqrt 2 - 1))) := by
    rw [innerValue]
    convert Real.hasDerivAt_arccos (x := 0) (by norm_num) (by norm_num) using 1 <;> norm_num
  convert (((arcDerivative.comp (Real.sqrt 2 - 1) innerDerivative).const_mul 2).sub_const
    Real.pi).div_const (Real.sqrt 2) using 1
  field_simp
  <;> ring

theorem separating_shapes_at_rhombus :
    separatingRadialShape (Real.sqrt 2 - 1) = 0 ∧
      separatingAngularShape (Real.sqrt 2 - 1) = 0 := by
  have polynomialZero : (Real.sqrt 2 - 1) ^ 2 + 2 * (Real.sqrt 2 - 1) - 1 = 0 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  constructor
  · simp [separatingRadialShape]
  · simp [separatingAngularShape, polynomialZero, Real.arccos_zero]
    <;> ring

theorem separatingUnstableShape_hasDerivAt_rhombus :
    HasDerivAt separatingUnstableShape (2 / (Real.sqrt 2 - 1)) (Real.sqrt 2 - 1) := by
  convert (separatingRadialShape_hasDerivAt_rhombus.add
    separatingAngularShape_hasDerivAt_rhombus).div_const 2 using 1
  ring

theorem separatingStableShape_hasDerivAt_rhombus :
    HasDerivAt separatingStableShape 0 (Real.sqrt 2 - 1) := by
  convert (separatingRadialShape_hasDerivAt_rhombus.sub
    separatingAngularShape_hasDerivAt_rhombus).div_const 2 using 1
  ring

theorem separating_shapes_incoming_slopes :
    Filter.Tendsto (fun rootRatio => separatingUnstableShape rootRatio / (rootRatio - (Real.sqrt 2 - 1)))
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1))) (nhds (2 / (Real.sqrt 2 - 1))) ∧
    Filter.Tendsto (fun rootRatio => separatingStableShape rootRatio / (rootRatio - (Real.sqrt 2 - 1)))
      (nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1))) (nhds 0) := by
  have filterLe : nhdsWithin (Real.sqrt 2 - 1) (Set.Ioi (Real.sqrt 2 - 1)) ≤
      nhdsWithin (Real.sqrt 2 - 1) ({Real.sqrt 2 - 1}ᶜ) := by
    apply nhdsWithin_mono
    intro value bounds
    exact ne_of_gt bounds
  have unstableZero : separatingUnstableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingUnstableShape, separating_shapes_at_rhombus]
  have stableZero : separatingStableShape (Real.sqrt 2 - 1) = 0 := by
    simp [separatingStableShape, separating_shapes_at_rhombus]
  constructor
  · have result := (hasDerivAt_iff_tendsto_slope.mp separatingUnstableShape_hasDerivAt_rhombus).mono_left filterLe
    change Filter.Tendsto (fun value => slope separatingUnstableShape (Real.sqrt 2 - 1) value) _ _ at result
    simpa only [slope_def_field, unstableZero, sub_zero] using result
  · have result := (hasDerivAt_iff_tendsto_slope.mp separatingStableShape_hasDerivAt_rhombus).mono_left filterLe
    change Filter.Tendsto (fun value => slope separatingStableShape (Real.sqrt 2 - 1) value) _ _ at result
    simpa only [slope_def_field, stableZero, sub_zero] using result

theorem separatingUnstableShape_incoming_exponential (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    ∃ coefficient > (0 : ℝ), Filter.Tendsto
      (fun time => Real.exp (-(2 * Real.sqrt 2 * frequency) * time) *
        separatingUnstableShape (separatingScalarOrbit frequency frequencyPositive time))
      Filter.atBot (nhds coefficient) := by
  obtain ⟨coefficient, coefficientPositive, exponentialLimit⟩ :=
    separatingScalarOrbit_incoming_exponential frequency frequencyPositive
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  refine ⟨coefficient * (2 / (Real.sqrt 2 - 1)), by positivity, ?_⟩
  have scalarWithin := tendsto_Ioo_atBot.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atBot
  have result := exponentialLimit.mul (separating_shapes_incoming_slopes.1.comp scalarWithin)
  apply result.congr'
  apply Filter.Eventually.of_forall
  intro time
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  change Real.exp _ * (_ - (Real.sqrt 2 - 1)) *
    (separatingUnstableShape (separatingScalarOrbit frequency frequencyPositive time) /
      (separatingScalarOrbit frequency frequencyPositive time - (Real.sqrt 2 - 1))) = _
  field_simp [(sub_pos.mpr bounds.1).ne']
  <;> ring

theorem separatingStableShape_incoming_ratio (frequency : ℝ) (frequencyPositive : 0 < frequency) :
    Filter.Tendsto (fun time => separatingStableShape (separatingScalarOrbit frequency frequencyPositive time) /
      separatingUnstableShape (separatingScalarOrbit frequency frequencyPositive time)) Filter.atBot (nhds 0) := by
  have rootPositive : 0 < Real.sqrt 2 - 1 := by linarith [sqrt_two_gt_one]
  have scalarWithin := tendsto_Ioo_atBot.mp
    (separatingQuadratureOrderIso frequency frequencyPositive).symm.tendsto_atBot
  have result := (separating_shapes_incoming_slopes.2.comp scalarWithin).div
    (separating_shapes_incoming_slopes.1.comp scalarWithin) (by positivity : (2 / (Real.sqrt 2 - 1) : ℝ) ≠ 0)
  simp only [zero_div] at result
  apply result.congr'
  apply Filter.Eventually.of_forall
  intro time
  change (_ / (separatingScalarOrbit frequency frequencyPositive time - (Real.sqrt 2 - 1))) /
    (_ / (separatingScalarOrbit frequency frequencyPositive time - (Real.sqrt 2 - 1))) = _
  have bounds := separatingScalarOrbit_mem frequency frequencyPositive time
  exact div_div_div_cancel_right₀ (sub_pos.mpr bounds.1).ne' _ _

end EulerNonuniqueness.Section2
