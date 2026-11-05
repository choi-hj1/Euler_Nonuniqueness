import Mathlib.Analysis.Calculus.Deriv.Mul

namespace EulerNonuniqueness.General

variable {Scalar Algebra : Type*} [NontriviallyNormedField Scalar]
  [NormedCommRing Algebra] [NormedAlgebra Scalar Algebra]

theorem hasDerivAt_pow_algebra {function : Scalar → Algebra} {derivative : Algebra} {point : Scalar}
    (actual : HasDerivAt function derivative point) (degree : ℕ) :
    HasDerivAt (fun current => function current ^ degree)
      ((degree : Algebra) * function point ^ (degree - 1) * derivative) point := by
  induction degree with
  | zero => simpa only [pow_zero, Nat.cast_zero, zero_mul] using hasDerivAt_const point (1 : Algebra)
  | succ degree induction =>
    cases degree with
    | zero => simpa using actual
    | succ degree =>
      have product := induction.mul actual
      convert product using 1
      · funext current
        rw [pow_succ]
      · simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one, pow_succ]
        ring

end EulerNonuniqueness.General
