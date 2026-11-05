import EulerNonuniqueness.Section3.ContourClosedMomentIdentities

noncomputable section

open MeasureTheory

namespace EulerNonuniqueness.Paper

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

theorem contour_value_sq_mul_tangent_integral_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi, data.val.1 label ^ 2 * data.val.2.val.1 label) = 0 := by
  have derivative (label : ℝ) : HasDerivAt (fun current => data.val.1 current ^ 3)
      ((3 : ℂ) * (data.val.1 label ^ 2 * data.val.2.val.1 label)) label := by
    convert ((PeriodicC1HolderHalf.hasDerivAt data label).mul
      (PeriodicC1HolderHalf.hasDerivAt data label)).mul (PeriodicC1HolderHalf.hasDerivAt data label) using 1
    · funext current
      ring
    · ring
  have integral := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label)
    ((continuous_const.mul ((data.val.1.continuous.pow 2).mul data.val.2.val.1.continuous)).intervalIntegrable (-Real.pi) Real.pi)
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [intervalIntegral.integral_const_mul, periodic, sub_self] at integral
  exact (mul_eq_zero.mp integral).resolve_left (by norm_num)

theorem contour_conjugate_square_derivative_integral_zero (data : PeriodicC1HolderHalf) :
    (∫ label in (-Real.pi)..Real.pi,
      star (data.val.1 label) ^ 2 * data.val.2.val.1 label +
        (2 : ℂ) * (data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label))) = 0 := by
  have conjugateDerivative (label : ℝ) : HasDerivAt (fun current => star (data.val.1 current))
      (star (data.val.2.val.1 label)) label := by
    exact (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt label
      (PeriodicC1HolderHalf.hasDerivAt data label)
  have derivative (label : ℝ) : HasDerivAt (fun current => data.val.1 current * star (data.val.1 current) ^ 2)
      (star (data.val.1 label) ^ 2 * data.val.2.val.1 label +
        (2 : ℂ) * (data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label))) label := by
    convert (PeriodicC1HolderHalf.hasDerivAt data label).mul
      ((conjugateDerivative label).mul (conjugateDerivative label)) using 1
    · funext current
      ring
    · ring
  have continuous : Continuous (fun label => star (data.val.1 label) ^ 2 * data.val.2.val.1 label +
      (2 : ℂ) * (data.val.1 label * star (data.val.1 label) * star (data.val.2.val.1 label))) := by
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun label _ => derivative label)
    (continuous.intervalIntegrable (-Real.pi) Real.pi)]
  have periodic := PeriodicC1HolderHalf.periodic data (-Real.pi)
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at periodic
  rw [periodic, sub_self]

end EulerNonuniqueness.Paper
