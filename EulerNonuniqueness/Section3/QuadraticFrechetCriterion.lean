import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Asymptotics.Lemmas

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

theorem hasFDerivAt_of_quadratic_remainder {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {function : E → F} {derivative : E →L[𝕜] F} {point : E} {radius constant : ℝ}
    (positive : 0 < radius)
    (bounded : ∀ increment, ‖increment‖ ≤ radius →
      ‖function (point + increment) - function point - derivative increment‖ ≤ constant * ‖increment‖ ^ 2) :
    HasFDerivAt function derivative point := by
  apply (hasFDerivAt_iff_isLittleO_nhds_zero (𝕜 := 𝕜) (f := function) (f' := derivative) (x := point)).mpr
  have estimate : (fun increment : E => function (point + increment) - function point - derivative increment)
      =O[𝓝 0] (fun increment : E => ‖increment‖ ^ 2) := by
    apply Asymptotics.IsBigO.of_bound constant
    filter_upwards [Metric.ball_mem_nhds (0 : E) positive] with increment member
    have small : ‖increment‖ ≤ radius :=
      (show ‖increment‖ < radius from by simpa only [mem_ball, dist_zero_right] using member).le
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖increment‖)] using bounded increment small
  exact estimate.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (E' := E) (by decide : 1 < (2 : ℕ)))

end EulerNonuniqueness.General
