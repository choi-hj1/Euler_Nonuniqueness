import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic

namespace EulerNonuniqueness.General

variable {Algebra : Type*} [NormedRing Algebra]

theorem inverse_perturbation_difference (base increment : Algebra)
    (baseUnit : IsUnit base) (sumUnit : IsUnit (base + increment)) :
    Ring.inverse (base + increment) - Ring.inverse base =
      -(Ring.inverse base * increment * Ring.inverse (base + increment)) := by
  calc
    _ = (Ring.inverse base * base) * Ring.inverse (base + increment) -
        Ring.inverse base * ((base + increment) * Ring.inverse (base + increment)) := by
      rw [Ring.inverse_mul_cancel base baseUnit, Ring.mul_inverse_cancel (base + increment) sumUnit,
        one_mul, mul_one]
    _ = _ := by noncomm_ring

theorem inverse_perturbation_linear_remainder (base increment : Algebra)
    (baseUnit : IsUnit base) (sumUnit : IsUnit (base + increment)) :
    Ring.inverse (base + increment) - Ring.inverse base +
        Ring.inverse base * increment * Ring.inverse base =
      Ring.inverse base * increment * Ring.inverse base * increment * Ring.inverse (base + increment) := by
  have difference := inverse_perturbation_difference base increment baseUnit sumUnit
  have reverse : Ring.inverse base - Ring.inverse (base + increment) =
      Ring.inverse base * increment * Ring.inverse (base + increment) := by
    rw [show Ring.inverse base - Ring.inverse (base + increment) =
      -(Ring.inverse (base + increment) - Ring.inverse base) by abel, difference, neg_neg]
  calc
    _ = Ring.inverse base * increment * (Ring.inverse base - Ring.inverse (base + increment)) := by
      rw [difference]
      noncomm_ring
    _ = _ := by rw [reverse]; noncomm_ring

theorem norm_inverse_perturbation_linear_remainder_le (base increment : Algebra)
    (baseUnit : IsUnit base) (sumUnit : IsUnit (base + increment)) :
    ‖Ring.inverse (base + increment) - Ring.inverse base +
        Ring.inverse base * increment * Ring.inverse base‖ ≤
      ‖Ring.inverse base‖ ^ 2 * ‖increment‖ ^ 2 * ‖Ring.inverse (base + increment)‖ := by
  rw [inverse_perturbation_linear_remainder base increment baseUnit sumUnit]
  have first := norm_mul_le (Ring.inverse base) increment
  have second := (norm_mul_le (Ring.inverse base * increment) (Ring.inverse base)).trans
    (mul_le_mul_of_nonneg_right first (norm_nonneg (Ring.inverse base)))
  have third := (norm_mul_le (Ring.inverse base * increment * Ring.inverse base) increment).trans
    (mul_le_mul_of_nonneg_right second (norm_nonneg increment))
  have fourth := (norm_mul_le (Ring.inverse base * increment * Ring.inverse base * increment)
    (Ring.inverse (base + increment))).trans
    (mul_le_mul_of_nonneg_right third (norm_nonneg (Ring.inverse (base + increment))))
  exact fourth.trans_eq (by ring)

theorem norm_inverse_perturbation_linear_remainder_le_uniform
    (base increment : Algebra) (baseUnit : IsUnit base) (sumUnit : IsUnit (base + increment))
    {inverseBound incrementBound size : ℝ}
    (baseBound : ‖Ring.inverse base‖ ≤ inverseBound)
    (sumBound : ‖Ring.inverse (base + increment)‖ ≤ inverseBound)
    (perturbationBound : ‖increment‖ ≤ incrementBound * size) :
    ‖Ring.inverse (base + increment) - Ring.inverse base +
        Ring.inverse base * increment * Ring.inverse base‖ ≤
      inverseBound ^ 3 * incrementBound ^ 2 * size ^ 2 := by
  calc
    _ ≤ ‖Ring.inverse base‖ ^ 2 * ‖increment‖ ^ 2 * ‖Ring.inverse (base + increment)‖ :=
      norm_inverse_perturbation_linear_remainder_le base increment baseUnit sumUnit
    _ ≤ inverseBound ^ 2 * (incrementBound * size) ^ 2 * inverseBound := by gcongr
    _ = _ := by ring

end EulerNonuniqueness.General
