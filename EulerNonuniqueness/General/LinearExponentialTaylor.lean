import EulerNonuniqueness.General.LinearExponentialCurve

namespace EulerNonuniqueness.General

noncomputable section

open Filter Asymptotics Set
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space] [CompleteSpace Space]

theorem linearExponentialCurve_second_order_remainder
    (operator : Space →L[ℝ] Space) (initial : Space) :
    (fun time : ℝ => linearExponentialCurve operator initial time - initial - time • operator initial -
      (time ^ 2 / 2) • operator (operator initial)) =o[𝓝 (0 : ℝ)] (fun time => time ^ 2) := by
  have first : deriv (linearExponentialCurve operator initial) =
      fun time => operator (linearExponentialCurve operator initial time) :=
    funext fun time => (linearExponentialCurve_hasDerivAt operator initial time).deriv
  have second : deriv (fun time => operator (linearExponentialCurve operator initial time)) =
      fun time => operator (operator (linearExponentialCurve operator initial time)) :=
    funext fun time => (linearExponentialCurve_second_hasDerivAt operator initial time).deriv
  have smooth : ContDiff ℝ 2 (linearExponentialCurve operator initial) := by
    rw [contDiff_iff_contDiffAt]
    intro time
    exact (linearExponentialCurve_analyticAt operator initial time).contDiffAt
  have peano := taylor_isLittleO (n := 2) (s := univ) (x₀ := (0 : ℝ)) convex_univ (mem_univ _) smooth.contDiffOn
  have polynomial (time : ℝ) : taylorWithinEval (linearExponentialCurve operator initial) 2 univ 0 time =
      initial + time • operator initial + (time ^ 2 / 2) • operator (operator initial) := by
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, iteratedDerivWithin_univ,
      iteratedDeriv_succ, iteratedDeriv_zero, first, second, linearExponentialCurve_zero,
      Nat.factorial_zero, Nat.factorial_one, Nat.factorial_succ, Nat.cast_one, Nat.cast_ofNat,
      one_mul, inv_one, sub_zero, pow_zero, pow_one, one_smul]
    congr 1
    ring
  have same (time : ℝ) :
      linearExponentialCurve operator initial time - taylorWithinEval (linearExponentialCurve operator initial) 2 univ 0 time =
      linearExponentialCurve operator initial time - initial - time • operator initial -
        (time ^ 2 / 2) • operator (operator initial) := by rw [polynomial]; abel
  simpa only [nhdsWithin_univ, same, sub_zero] using peano

end

end EulerNonuniqueness.General
