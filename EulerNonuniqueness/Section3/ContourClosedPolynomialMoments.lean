import EulerNonuniqueness.Section3.ContourPolynomialMomentLine
import EulerNonuniqueness.Section3.RelabeledDiskForcingPrimitive
import EulerNonuniqueness.General.DerivAlgebraPower

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem contour_value_power_mul_tangent_integral_zero (data : PeriodicC1HolderHalf) (degree : ℕ) :
    (∫ label in (-Real.pi)..Real.pi, data.val.1 label ^ degree * data.val.2.val.1 label) = 0 := by
  have derivative (label : ℝ) : HasDerivAt (fun current => data.val.1 current ^ (degree + 1))
      (((degree + 1 : ℕ) : ℂ) * (data.val.1 label ^ degree * data.val.2.val.1 label)) label := by
    simpa only [Nat.add_sub_cancel, mul_assoc] using
      EulerNonuniqueness.General.hasDerivAt_pow_algebra (PeriodicC1HolderHalf.hasDerivAt data label) (degree + 1)
  have integrable : IntervalIntegrable (fun label =>
      ((degree + 1 : ℕ) : ℂ) * (data.val.1 label ^ degree * data.val.2.val.1 label))
      volume (-Real.pi) Real.pi := by
    apply Continuous.intervalIntegrable
    fun_prop
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label) integrable
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [intervalIntegral.integral_const_mul, periodic, sub_self] at integral
  exact (mul_eq_zero.mp integral).resolve_left (by exact_mod_cast Nat.succ_ne_zero degree)

theorem c1NaturalPower_tangent (data : PeriodicC1HolderHalf) (degree : ℕ) (label : ℝ) :
    (c1NaturalPower data degree).val.2.val.1 label =
      (degree : ℂ) * data.val.1 label ^ (degree - 1) * data.val.2.val.1 label := by
  have polynomial := EulerNonuniqueness.General.hasDerivAt_pow_algebra
    (PeriodicC1HolderHalf.hasDerivAt data label) degree
  have actual := PeriodicC1HolderHalf.hasDerivAt (c1NaturalPower data degree) label
  have identity : (fun current : ℝ => (c1NaturalPower data degree).val.1 current) =
      fun current => data.val.1 current ^ degree := funext (c1NaturalPower_value data degree)
  change HasDerivAt (fun current : ℝ => (c1NaturalPower data degree).val.1 current)
    ((c1NaturalPower data degree).val.2.val.1 label) label at actual
  rw [identity] at actual
  exact actual.unique polynomial

theorem contour_conjugate_power_product_derivative_integral_zero
    (data : PeriodicC1HolderHalf) (degree : ℕ) :
    (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label +
        ((degree + 1 : ℕ) : ℂ) *
          (data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))) = 0 := by
  have conjugateDerivative (label : ℝ) : HasDerivAt (fun current => star (data.val.1 current))
      (star (data.val.2.val.1 label)) label :=
    (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt label
      (PeriodicC1HolderHalf.hasDerivAt data label)
  have derivative (label : ℝ) : HasDerivAt
      (fun current => data.val.1 current * star (data.val.1 current) ^ (degree + 1))
      (star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label +
        ((degree + 1 : ℕ) : ℂ) *
          (data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))) label := by
    have product := (PeriodicC1HolderHalf.hasDerivAt data label).mul
      (EulerNonuniqueness.General.hasDerivAt_pow_algebra (conjugateDerivative label) (degree + 1))
    convert product using 1
    simp only [Nat.add_sub_cancel]
    ring
  have continuous : Continuous (fun label =>
      star (data.val.1 label) ^ (degree + 1) * data.val.2.val.1 label +
        ((degree + 1 : ℕ) : ℂ) *
          (data.val.1 label * star (data.val.1 label) ^ degree * star (data.val.2.val.1 label))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label)
    (continuous.intervalIntegrable (-Real.pi) Real.pi)]
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [periodic, sub_self]

end EulerNonuniqueness.Paper
