import Mathlib.Analysis.Calculus.Taylor

namespace EulerNonuniqueness.General

noncomputable section

open Filter Asymptotics Set
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem second_order_peano_at_zero
    (function derivative : ℝ → Space) (second : Space)
    (first : ∀ᶠ time in 𝓝 (0 : ℝ), HasDerivAt function (derivative time) time)
    (secondDerivative : HasDerivAt derivative second 0) :
    (fun time => function time - function 0 - time • derivative 0 -
      (time ^ 2 / 2) • second) =o[𝓝 (0 : ℝ)] (fun time => time ^ 2) := by
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp first
  let residual := fun time : ℝ => function time - function 0 - time • derivative 0 -
    (time ^ 2 / 2) • second
  let residualDerivative := fun time : ℝ => derivative time - derivative 0 - time • second
  have derivativeLittle : residualDerivative =o[𝓝 (0 : ℝ)] (fun time => time) := by
    simpa only [zero_add] using (hasDerivAt_iff_isLittleO_nhds_zero.mp secondDerivative)
  have actual (time : ℝ) (inside : time ∈ Metric.ball (0 : ℝ) radius) :
      HasDerivAt residual (residualDerivative time) time := by
    have polynomial : HasDerivAt (fun value : ℝ => value ^ 2 / 2) time time := by
      convert ((hasDerivAt_id time).pow 2).div_const 2 using 1 <;> simp <;> ring
    convert (((contained inside).sub_const (function 0)).sub
      ((hasDerivAt_id time).smul_const (derivative 0))).sub
      (polynomial.smul_const second) using 1 <;> simp [residual, residualDerivative]
  have peano := (convex_ball (0 : ℝ) radius).isLittleO_pow_succ_real
    (n := 1) (Metric.mem_ball_self positive)
    (fun time inside => (actual time inside).hasDerivWithinAt)
    (by simpa only [sub_zero, pow_one] using derivativeLittle.mono nhdsWithin_le_nhds)
  have filters : 𝓝[Metric.ball (0 : ℝ) radius] (0 : ℝ) = 𝓝 (0 : ℝ) :=
    nhdsWithin_eq_nhds.mpr (Metric.ball_mem_nhds _ positive)
  simpa [filters, residual] using peano

end

end EulerNonuniqueness.General
