import EulerNonuniqueness.Section3.CenteredAntiholomorphicAnalytic

namespace EulerNonuniqueness.Paper

noncomputable section

open MeasureTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

local instance circlePositiveMomentsC1Group : NormedAddCommGroup PeriodicC1HolderHalf :=
  Submodule.normedAddCommGroup periodicC1HolderGraph

attribute [local instance] forcingModeC1RealSpace forcingModeC1ComplexModule forcingModeC1ComplexSpace

theorem contourPolynomialMoment_circle_positive (degree : ℕ) :
    contourPolynomialMoment (degree + 1) standardCircleBanach = 0 := by
  change (-Complex.I / 2) * (∫ label in (-Real.pi)..Real.pi,
    standardCircle label ^ (degree + 1) * star (standardCircle label) *
      (Complex.I * standardCircle label)) = 0
  have integrand (label : ℝ) : standardCircle label ^ (degree + 1) * star (standardCircle label) *
      (Complex.I * standardCircle label) = Complex.I * standardCircle label ^ (degree + 1) := by
    have nonzero : standardCircle label ≠ 0 := by simp [standardCircle, Complex.exp_ne_zero]
    have unit : star (standardCircle label) * standardCircle label = 1 := by
      rw [standardCircle_star_eq_inv, inv_mul_cancel₀ nonzero]
    calc
      _ = Complex.I * standardCircle label ^ (degree + 1) *
          (star (standardCircle label) * standardCircle label) := by ring
      _ = _ := by rw [unit, mul_one]
  simp_rw [integrand]
  rw [intervalIntegral.integral_const_mul, integral_standardCircle_pow_succ]
  simp

end

end EulerNonuniqueness.Paper
