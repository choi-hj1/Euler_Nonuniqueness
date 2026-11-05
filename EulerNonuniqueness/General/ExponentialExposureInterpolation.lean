import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

namespace EulerNonuniqueness.General

theorem exponential_exposure_interpolation
    {seed endpoint theta fast slow origin finish : ℝ}
    (seedPositive : 0 < seed) (endpointPositive : 0 < endpoint)
    (thetaNonnegative : 0 ≤ theta) (_thetaLeOne : theta ≤ 1)
    (ordered : origin ≤ finish) (slowBound : slow ≤ theta * fast)
    (exposure : seed * Real.exp (fast * (finish - origin)) ≤ endpoint) :
    seed * Real.exp (slow * (finish - origin)) ≤ seed ^ (1 - theta) * endpoint ^ theta := by
  have logarithmic := Real.log_le_log (mul_pos seedPositive (Real.exp_pos _)) exposure
  rw [Real.log_mul seedPositive.ne' (Real.exp_pos _).ne', Real.log_exp] at logarithmic
  have scaled := mul_le_mul_of_nonneg_left logarithmic thetaNonnegative
  have slowScaled := mul_le_mul_of_nonneg_right slowBound (sub_nonneg.mpr ordered)
  calc
    seed * Real.exp (slow * (finish - origin)) =
        Real.exp (Real.log seed + slow * (finish - origin)) := by
      rw [Real.exp_add, Real.exp_log seedPositive]
    _ ≤ Real.exp ((1 - theta) * Real.log seed + theta * Real.log endpoint) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [scaled, slowScaled]
    _ = seed ^ (1 - theta) * endpoint ^ theta := by
      rw [Real.rpow_def_of_pos seedPositive, Real.rpow_def_of_pos endpointPositive,
        ← Real.exp_add]
      congr 1
      ring

end EulerNonuniqueness.General
