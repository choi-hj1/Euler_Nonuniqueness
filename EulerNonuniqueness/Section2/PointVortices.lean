import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Section 2: exact point-vortex and shape algebra

Source: `nonuniqueness_euler_ver1.tex`, Section 2, equations `point-ode`,
`shape-ode`, `shape-linearization`, `adjusted-phase`, and `pair-distances`.

This file proves the algebraic identities used in the paper. The actual
time-dependent complex solution of Proposition 2.1 is proved in
`RotatingRhombus.lean`. This file does not prove Proposition 2.2.
-/

namespace EulerNonuniqueness.Section2

noncomputable section

section FieldIdentities

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜]

theorem positive_vortex_velocity (first second : 𝕜)
    (first_ne : first ≠ 0) (difference_ne : first - second ≠ 0)
    (sum_ne : first + second ≠ 0) :
    1 / (2 * first) - 1 / (first - second) - 1 / (first + second) =
      -(3 * first ^ 2 + second ^ 2) / (2 * first * (first ^ 2 - second ^ 2)) := by
  have squares_ne : first ^ 2 - second ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero sum_ne difference_ne
  field_simp [first_ne, difference_ne, sum_ne, squares_ne]
  ring

theorem negative_vortex_velocity (first second : 𝕜)
    (second_ne : second ≠ 0) (difference_ne : first - second ≠ 0)
    (sum_ne : first + second ≠ 0) :
    1 / (second - first) + 1 / (second + first) - 1 / (2 * second) =
      -(first ^ 2 + 3 * second ^ 2) / (2 * second * (first ^ 2 - second ^ 2)) := by
  have reverse_ne : second - first ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp difference_ne))
  have reverse_sum_ne : second + first ≠ 0 := by simpa [add_comm] using sum_ne
  have squares_ne : first ^ 2 - second ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero sum_ne difference_ne
  field_simp [second_ne, reverse_ne, reverse_sum_ne, squares_ne]
  ring

theorem angular_impulse_algebra (first second : 𝕜)
    (first_ne : first ≠ 0) (second_ne : second ≠ 0)
    (squares_ne : first ^ 2 - second ^ 2 ≠ 0) :
    first * (-(3 * first ^ 2 + second ^ 2) /
      (2 * first * (first ^ 2 - second ^ 2))) -
    second * (-(first ^ 2 + 3 * second ^ 2) /
      (2 * second * (first ^ 2 - second ^ 2))) = -1 := by
  field_simp [first_ne, second_ne, squares_ne]
  ring

omit [CharZero 𝕜] in
theorem second_moment_identity (circulation first second : 𝕜) :
    circulation * first ^ 2 + circulation * (-first) ^ 2 -
      circulation * second ^ 2 - circulation * (-second) ^ 2 =
        2 * circulation * (first ^ 2 - second ^ 2) := by
  ring

theorem second_moment_dipole_identity (circulation first second : 𝕜) :
    2 * circulation * (first ^ 2 - second ^ 2) =
      4 * circulation * ((first + second) / 2) * (first - second) := by
  ring

omit [CharZero 𝕜] in
theorem quadrupole_far_field_identity (position first second : 𝕜)
    (first_difference_ne : position - first ≠ 0)
    (first_sum_ne : position + first ≠ 0)
    (second_difference_ne : position - second ≠ 0)
    (second_sum_ne : position + second ≠ 0) :
    1 / (position - first) + 1 / (position + first) -
      1 / (position - second) - 1 / (position + second) =
        2 * position * (first ^ 2 - second ^ 2) /
          ((position ^ 2 - first ^ 2) * (position ^ 2 - second ^ 2)) := by
  have first_squares_ne : position ^ 2 - first ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero first_sum_ne first_difference_ne
  have second_squares_ne : position ^ 2 - second ^ 2 ≠ 0 := by
    rw [sq_sub_sq]
    exact mul_ne_zero second_sum_ne second_difference_ne
  field_simp [first_difference_ne, first_sum_ne, second_difference_ne, second_sum_ne,
    first_squares_ne, second_squares_ne]
  ring

end FieldIdentities

theorem angular_impulse_real_cancellation (coefficient : ℝ) (first second : ℂ)
    (first_ne : first ≠ 0) (second_ne : second ≠ 0)
    (squares_ne : first ^ 2 - second ^ 2 ≠ 0) :
    2 * (first * (Complex.I * coefficient *
      (-(3 * first ^ 2 + second ^ 2) / (2 * first * (first ^ 2 - second ^ 2)))) -
      second * (Complex.I * coefficient *
        (-(first ^ 2 + 3 * second ^ 2) / (2 * second * (first ^ 2 - second ^ 2))))).re = 0 := by
  have cancellation := angular_impulse_algebra first second first_ne second_ne squares_ne
  have factorization :
      first * (Complex.I * coefficient *
        (-(3 * first ^ 2 + second ^ 2) / (2 * first * (first ^ 2 - second ^ 2)))) -
      second * (Complex.I * coefficient *
        (-(first ^ 2 + 3 * second ^ 2) / (2 * second * (first ^ 2 - second ^ 2)))) =
      Complex.I * coefficient *
        (first * (-(3 * first ^ 2 + second ^ 2) / (2 * first * (first ^ 2 - second ^ 2))) -
          second * (-(first ^ 2 + 3 * second ^ 2) / (2 * second * (first ^ 2 - second ^ 2)))) := by
    ring
  rw [factorization, cancellation]
  simp

def rhombusRatio : ℝ := 3 - 2 * Real.sqrt 2

theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonnegative := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have nonnegative := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem rhombusRatio_pos : 0 < rhombusRatio := by
  unfold rhombusRatio
  linarith [sqrt_two_lt_three_halves]

theorem rhombusRatio_lt_one : rhombusRatio < 1 := by
  unfold rhombusRatio
  linarith [sqrt_two_gt_one]

theorem rhombusRatio_quadratic : rhombusRatio ^ 2 - 6 * rhombusRatio + 1 = 0 := by
  unfold rhombusRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem rhombusRatio_square : rhombusRatio = (Real.sqrt 2 - 1) ^ 2 := by
  unfold rhombusRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem rhombusRatio_quotient :
    (Real.sqrt 2 - 1) / (Real.sqrt 2 + 1) = rhombusRatio := by
  have denominator_ne : Real.sqrt 2 + 1 ≠ 0 := by linarith [sqrt_two_gt_one]
  apply (div_eq_iff denominator_ne).2
  unfold rhombusRatio
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

def radialVelocity (frequency ratio phase : ℝ) : ℝ :=
  -4 * frequency * ratio * (1 - ratio) ^ 2 * Real.sin phase /
    (1 + ratio ^ 2 - 2 * ratio * Real.cos phase)

def shapeAngleVelocity (frequency ratio phase : ℝ) : ℝ :=
  -frequency * (1 - ratio ^ 2) * (1 - 4 * ratio + ratio ^ 2 + 2 * ratio * Real.cos phase) /
    (ratio * (1 + ratio ^ 2 - 2 * ratio * Real.cos phase))

def rotationVelocity (frequency ratio phase : ℝ) : ℝ :=
  -frequency * (1 - ratio) * (3 - 2 * ratio * Real.cos phase - ratio ^ 2) /
    (2 * (1 + ratio ^ 2 - 2 * ratio * Real.cos phase))

theorem radialVelocity_at_rhombus (frequency : ℝ) :
    radialVelocity frequency rhombusRatio Real.pi = 0 := by
  simp [radialVelocity]

theorem shapeAngleVelocity_at_rhombus (frequency : ℝ) :
    shapeAngleVelocity frequency rhombusRatio Real.pi = 0 := by
  have numerator : 1 - 4 * rhombusRatio + rhombusRatio ^ 2 +
      2 * rhombusRatio * Real.cos Real.pi = 0 := by
    rw [Real.cos_pi]
    nlinarith [rhombusRatio_quadratic]
  simp only [shapeAngleVelocity, numerator, mul_zero, zero_div]

theorem rotationVelocity_at_rhombus (frequency : ℝ) :
    rotationVelocity frequency rhombusRatio Real.pi = -frequency := by
  unfold rotationVelocity
  rw [Real.cos_pi]
  apply (div_eq_iff (by
    nlinarith [rhombusRatio_pos, sq_nonneg rhombusRatio])).2
  linear_combination -frequency * (rhombusRatio + 1) * rhombusRatio_quadratic

theorem rotating_rhombus_shape_solution (frequency initialPhase time : ℝ) :
    HasDerivAt (fun _ : ℝ => rhombusRatio)
      (radialVelocity frequency rhombusRatio Real.pi) time ∧
    HasDerivAt (fun _ : ℝ => Real.pi)
      (shapeAngleVelocity frequency rhombusRatio Real.pi) time ∧
    HasDerivAt (fun currentTime : ℝ => initialPhase - frequency * currentTime)
      (rotationVelocity frequency rhombusRatio Real.pi) time := by
  rw [radialVelocity_at_rhombus, shapeAngleVelocity_at_rhombus,
    rotationVelocity_at_rhombus]
  refine ⟨hasDerivAt_const time rhombusRatio, hasDerivAt_const time Real.pi, ?_⟩
  simpa using (hasDerivAt_const time initialPhase).sub
    ((hasDerivAt_id time).const_mul frequency)

theorem radialVelocity_phase_derivative (frequency : ℝ) :
    HasDerivAt (fun phase => radialVelocity frequency rhombusRatio phase)
      (2 * frequency * rhombusRatio) Real.pi := by
  have denominator_ne :
      1 + rhombusRatio ^ 2 - 2 * rhombusRatio * Real.cos Real.pi ≠ 0 := by
    rw [Real.cos_pi]
    nlinarith [rhombusRatio_pos, sq_nonneg rhombusRatio]
  have numerator_derivative := (Real.hasDerivAt_sin Real.pi).const_mul
    (-4 * frequency * rhombusRatio * (1 - rhombusRatio) ^ 2)
  have denominator_derivative := (hasDerivAt_const Real.pi (1 + rhombusRatio ^ 2)).sub
    ((Real.hasDerivAt_cos Real.pi).const_mul (2 * rhombusRatio))
  have quotient_derivative := numerator_derivative.div denominator_derivative denominator_ne
  have square_relation : 2 * (1 - rhombusRatio) ^ 2 =
      1 + rhombusRatio ^ 2 + 2 * rhombusRatio := by
    nlinarith [rhombusRatio_quadratic]
  convert quotient_derivative using 1
  simp only [Real.cos_pi, Real.sin_pi, neg_zero, mul_zero, sub_zero, mul_neg,
    mul_one, neg_neg]
  have positive_denominator : 0 < 1 + rhombusRatio ^ 2 + 2 * rhombusRatio := by
    nlinarith [rhombusRatio_pos, sq_nonneg rhombusRatio]
  have derivative_identity :
      4 * frequency * rhombusRatio * (1 - rhombusRatio) ^ 2 =
        2 * frequency * rhombusRatio *
          (1 + rhombusRatio ^ 2 + 2 * rhombusRatio) := by
    nlinarith [congrArg (fun value : ℝ => 2 * frequency * rhombusRatio * value)
      square_relation]
  field_simp
  nlinarith [congrArg (fun value : ℝ =>
    value * (1 + rhombusRatio ^ 2 + 2 * rhombusRatio)) derivative_identity]

theorem radialVelocity_ratio_derivative (frequency : ℝ) :
    HasDerivAt (fun ratio => radialVelocity frequency ratio Real.pi) 0 rhombusRatio := by
  simpa [radialVelocity] using (hasDerivAt_const rhombusRatio (0 : ℝ))

theorem shapeAngleVelocity_phase_derivative (frequency : ℝ) :
    HasDerivAt (fun phase => shapeAngleVelocity frequency rhombusRatio phase)
      0 Real.pi := by
  have cosine_derivative : HasDerivAt Real.cos 0 Real.pi := by
    simpa using Real.hasDerivAt_cos Real.pi
  have numerator_derivative :=
    ((hasDerivAt_const Real.pi (1 - 4 * rhombusRatio + rhombusRatio ^ 2)).add
      (cosine_derivative.const_mul (2 * rhombusRatio))).const_mul
        (-frequency * (1 - rhombusRatio ^ 2))
  have denominator_derivative :=
    ((hasDerivAt_const Real.pi (1 + rhombusRatio ^ 2)).sub
      (cosine_derivative.const_mul (2 * rhombusRatio))).const_mul rhombusRatio
  have denominator_ne : rhombusRatio *
      (1 + rhombusRatio ^ 2 - 2 * rhombusRatio * Real.cos Real.pi) ≠ 0 := by
    apply mul_ne_zero (ne_of_gt rhombusRatio_pos)
    rw [Real.cos_pi]
    nlinarith [rhombusRatio_pos, sq_nonneg rhombusRatio]
  simpa [shapeAngleVelocity] using
    numerator_derivative.div denominator_derivative denominator_ne

theorem shapeAngleVelocity_ratio_derivative (frequency : ℝ) :
    HasDerivAt (fun ratio => shapeAngleVelocity frequency ratio Real.pi)
      (4 * frequency / rhombusRatio) rhombusRatio := by
  have numerator_factor : HasDerivAt (fun ratio : ℝ => 1 - 6 * ratio + ratio ^ 2)
      (-6 + 2 * rhombusRatio) rhombusRatio := by
    convert ((hasDerivAt_const rhombusRatio (1 : ℝ)).sub
      ((hasDerivAt_id rhombusRatio).const_mul 6)).add
        ((hasDerivAt_id rhombusRatio).pow 2) using 1
    simp only [id_eq]
    ring
  have zero_factor : 1 - 6 * rhombusRatio + rhombusRatio ^ 2 = 0 := by
    nlinarith [rhombusRatio_quadratic]
  have impulse_factor := (hasDerivAt_const rhombusRatio (1 : ℝ)).sub
    ((hasDerivAt_id rhombusRatio).pow 2)
  have numerator_derivative := (impulse_factor.mul numerator_factor).const_mul (-frequency)
  have denominator_derivative := (hasDerivAt_id rhombusRatio).mul
    (((hasDerivAt_const rhombusRatio (1 : ℝ)).add
      ((hasDerivAt_id rhombusRatio).pow 2)).add
        ((hasDerivAt_id rhombusRatio).const_mul 2))
  have denominator_factor_pos : 0 < 1 + rhombusRatio ^ 2 + 2 * rhombusRatio := by
    nlinarith [rhombusRatio_pos, sq_nonneg rhombusRatio]
  have denominator_ne : rhombusRatio *
      (1 + rhombusRatio ^ 2 + 2 * rhombusRatio) ≠ 0 :=
    mul_ne_zero (ne_of_gt rhombusRatio_pos) (ne_of_gt denominator_factor_pos)
  have quotient_derivative := numerator_derivative.div denominator_derivative denominator_ne
  have polynomial_identity : (1 - rhombusRatio ^ 2) * (6 - 2 * rhombusRatio) =
      4 * (1 + rhombusRatio ^ 2 + 2 * rhombusRatio) := by
    linear_combination (2 * rhombusRatio + 2) * rhombusRatio_quadratic
  convert quotient_derivative using 1
  · funext ratio
    simp only [shapeAngleVelocity, Real.cos_pi, id_eq]
    congr 1 <;> ring
  · simp only [id_eq, zero_factor, mul_zero, zero_mul, zero_add, sub_zero]
    have numerator_identity :
        -frequency * ((1 - rhombusRatio ^ 2) * (-6 + 2 * rhombusRatio)) =
          4 * frequency * (1 + rhombusRatio ^ 2 + 2 * rhombusRatio) := by
      linear_combination frequency * polynomial_identity
    rw [numerator_identity]
    field_simp [ne_of_gt rhombusRatio_pos, ne_of_gt denominator_factor_pos]
    ring

theorem shape_linearization_diagonalization (frequency horizontal vertical : ℝ) :
    ((2 * Real.sqrt 2 * frequency * vertical +
        2 * Real.sqrt 2 * frequency * horizontal) / 2 =
      2 * Real.sqrt 2 * frequency * ((horizontal + vertical) / 2)) ∧
    ((2 * Real.sqrt 2 * frequency * vertical -
        2 * Real.sqrt 2 * frequency * horizontal) / 2 =
      -(2 * Real.sqrt 2 * frequency) * ((horizontal - vertical) / 2)) := by
  constructor <;> ring

theorem adjusted_phase_linear_cancellation (frequency horizontal : ℝ) :
    (-frequency + frequency * (Real.sqrt 2 - 1) * horizontal) -
      ((Real.sqrt 2 - 1) / 4) * (4 * frequency * horizontal) = -frequency := by
  ring

theorem adjusted_phase_remainder_identity
    (frequency horizontal rotationError shapeError : ℝ) :
    (-frequency + frequency * (Real.sqrt 2 - 1) * horizontal + rotationError) -
      ((Real.sqrt 2 - 1) / 4) * (4 * frequency * horizontal + shapeError) =
        -frequency + rotationError - ((Real.sqrt 2 - 1) / 4) * shapeError := by
  ring

theorem separating_trigonometric_identity (rootRatio : ℝ) :
    (rootRatio ^ 4 + 4 * rootRatio ^ 3 - 4 * rootRatio + 1) ^ 2 +
      (rootRatio ^ 2 + 2 * rootRatio - 1) ^ 2 *
        (1 - rootRatio ^ 2) * (rootRatio ^ 2 + 4 * rootRatio - 1) =
          4 * rootRatio ^ 4 := by
  ring

theorem pair_distance_sum (length rootRatio : ℝ)
    (below_one : rootRatio < 1) (above_neg_one : -1 < rootRatio) :
    2 * length ^ 2 / (1 + rootRatio) + 2 * length ^ 2 * rootRatio / (1 - rootRatio) =
      2 * length ^ 2 * (1 + rootRatio ^ 2) / (1 - rootRatio ^ 2) := by
  have sum_ne : 1 + rootRatio ≠ 0 := by linarith
  have difference_ne : 1 - rootRatio ≠ 0 := by linarith
  have squares_ne : 1 - rootRatio ^ 2 ≠ 0 := by
    nlinarith [mul_pos (show 0 < 1 - rootRatio by linarith)
      (show 0 < 1 + rootRatio by linarith)]
  field_simp [sum_ne, difference_ne, squares_ne]
  ring

theorem pair_distance_product (length rootRatio : ℝ)
    (below_one : rootRatio < 1) (above_neg_one : -1 < rootRatio) :
    (2 * length ^ 2 / (1 + rootRatio)) * (2 * length ^ 2 * rootRatio / (1 - rootRatio)) =
      4 * length ^ 4 * rootRatio / (1 - rootRatio ^ 2) := by
  have sum_ne : 1 + rootRatio ≠ 0 := by linarith
  have difference_ne : 1 - rootRatio ≠ 0 := by linarith
  have squares_ne : 1 - rootRatio ^ 2 ≠ 0 := by
    nlinarith [mul_pos (show 0 < 1 - rootRatio by linarith)
      (show 0 < 1 + rootRatio by linarith)]
  field_simp [sum_ne, difference_ne, squares_ne]
  ring

theorem scalar_orbit_positive (frequency rootRatio : ℝ)
    (frequency_pos : 0 < frequency) (above_rhombus : Real.sqrt 2 - 1 < rootRatio)
    (below_one : rootRatio < 1) :
    0 < frequency / 4 * (1 - rootRatio ^ 2) ^ (3 / 2 : ℝ) / rootRatio ^ 2 *
      (rootRatio ^ 2 + 2 * rootRatio - 1) * Real.sqrt (rootRatio ^ 2 + 4 * rootRatio - 1) := by
  have root_pos : 0 < rootRatio := by linarith [sqrt_two_gt_one]
  have first_factor_pos : 0 < rootRatio ^ 2 + 2 * rootRatio - 1 := by
    have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have product_pos := mul_pos
      (show 0 < rootRatio - (Real.sqrt 2 - 1) by linarith)
      (show 0 < rootRatio + Real.sqrt 2 + 1 by linarith [sqrt_two_gt_one])
    nlinarith
  have second_factor_pos : 0 < rootRatio ^ 2 + 4 * rootRatio - 1 := by
    nlinarith
  have endpoint_factor_pos : 0 < 1 - rootRatio ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - rootRatio by linarith)
      (show 0 < 1 + rootRatio by linarith)]
  positivity

def optimalForcingCoefficient (circulation frequency centerDistance : ℝ) : ℝ :=
  Real.sqrt 3 * circulation ^ 2 /
    (2 * Real.sqrt 2 * Real.pi ^ 2 * frequency ^ 2 * centerDistance ^ 4)

theorem optimalForcingCoefficient_pos (circulation frequency centerDistance : ℝ)
    (circulation_pos : 0 < circulation) (frequency_pos : 0 < frequency)
    (distance_pos : 0 < centerDistance) :
    0 < optimalForcingCoefficient circulation frequency centerDistance := by
  unfold optimalForcingCoefficient
  have pi_pos := Real.pi_pos
  positivity

theorem forcing_coefficient_amplitude_algebra (scale : ℝ) :
    (-scale / 2) ^ 2 + (Real.sqrt 2 * scale / 4) ^ 2 =
      3 * scale ^ 2 / 8 := by
  have square := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  nlinarith [congrArg (fun value : ℝ => value * scale ^ 2) square]

end

end EulerNonuniqueness.Section2
