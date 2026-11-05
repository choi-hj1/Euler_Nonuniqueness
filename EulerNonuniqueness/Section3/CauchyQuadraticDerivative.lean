import EulerNonuniqueness.Section3.CauchyCubicRemainder
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

open Set Metric Complex Filter
open scoped Topology NNReal

namespace EulerNonuniqueness.Paper

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem cauchyQuadraticCoefficient_second_derivative {function : ℂ → E} {radius : ℝ≥0}
    (positive : 0 < radius) (holomorphic : DiffContOnCl ℂ function (ball 0 radius)) :
    (2 : ℂ) • cauchyQuadraticCoefficient function radius = deriv (deriv function) 0 := by
  have integrable : CircleIntegrable function 0 radius :=
    ContinuousOn.circleIntegrable radius.coe_nonneg
      (holomorphic.continuousOn_ball.mono sphere_subset_closedBall)
  have series := hasFPowerSeriesOn_cauchy_integral integrable positive
  have equality : (fun position => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ parameter in C(0, radius), (parameter - position)⁻¹ • function parameter) =ᶠ[𝓝 0] function := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) positive] with position member
    exact holomorphic.two_pi_i_inv_smul_circleIntegral_sub_inv_smul member
  have coefficient := series.factorial_smul (1 : ℂ) 2
  rw [← iteratedDeriv_eq_iteratedFDeriv, equality.iteratedDeriv_eq 2] at coefficient
  simpa only [cauchyPowerSeries, ContinuousMultilinearMap.mkPiRing_apply,
    Finset.prod_const_one, one_smul, sub_zero, Nat.factorial_two,
    show iteratedDeriv 2 function = deriv (deriv function) by
      rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero],
    cauchyQuadraticCoefficient, ← Nat.cast_smul_eq_nsmul ℂ,
    Nat.cast_ofNat, ← mul_smul, ← pow_succ, one_mul, Nat.reduceAdd] using coefficient

end

end EulerNonuniqueness.Paper
