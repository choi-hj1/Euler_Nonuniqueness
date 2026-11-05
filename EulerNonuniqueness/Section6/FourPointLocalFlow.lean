import EulerNonuniqueness.Section6.FourPointImpulseControl
import Mathlib.Analysis.ODE.PicardLindelof

noncomputable section

open Set Filter
open scoped Topology

namespace EulerNonuniqueness.Section6

theorem fourPointNoncollision_eventually {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) :
    ∀ᶠ current in 𝓝 positions, FourPointNoncollision current := by
  apply eventually_all.mpr
  intro target
  apply eventually_all.mpr
  intro source
  by_cases distinct : source ≠ target
  · have continuous : ContinuousAt (fun current : FourPointConfiguration => current target - current source) positions := by
      fun_prop
    filter_upwards [continuous.eventually_ne (noncollision target source distinct)] with current currentNonzero
    exact fun _ => currentNonzero
  · exact Eventually.of_forall (by simp [distinct])

theorem fourPointField_local_solution (coefficient : ℝ) {positions : FourPointConfiguration}
    (noncollision : FourPointNoncollision positions) :
    ∃ trajectory : ℝ → FourPointConfiguration, trajectory 0 = positions ∧
      ∃ radius > (0 : ℝ), ∀ time ∈ Ioo (-radius) radius,
        FourPointNoncollision (trajectory time) ∧
          HasDerivAt trajectory (fourPointField coefficient (trajectory time)) time := by
  have smooth : ContDiffAt ℝ 1 (fourPointField coefficient) positions :=
    (fourPointField_contDiffAt coefficient noncollision).of_le (by norm_num)
  obtain ⟨trajectory, initial, radius, radiusPositive, equation⟩ :=
    exists_forall_hasDerivAt_Ioo_eq_of_contDiffAt (0 : ℝ) smooth
  have zeroInside : (0 : ℝ) ∈ Ioo (0 - radius) (0 + radius) := by constructor <;> linarith
  have continuous : ContinuousAt trajectory 0 := (equation 0 zeroInside).continuousAt
  have collisionFree : ∀ᶠ time in 𝓝 (0 : ℝ), FourPointNoncollision (trajectory time) :=
    continuous.tendsto.eventually (by simpa only [initial] using fourPointNoncollision_eventually noncollision)
  obtain ⟨collisionRadius, collisionRadiusPositive, collisionBall⟩ := Metric.mem_nhds_iff.mp collisionFree
  refine ⟨trajectory, initial, min radius collisionRadius, lt_min radiusPositive collisionRadiusPositive, ?_⟩
  intro time timeInside
  have radiusBound := min_le_left radius collisionRadius
  have collisionBound := min_le_right radius collisionRadius
  refine ⟨collisionBall ?_, equation time ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact abs_lt.mpr ⟨by linarith [timeInside.1], by linarith [timeInside.2]⟩
  · constructor <;> linarith [timeInside.1, timeInside.2]

end EulerNonuniqueness.Section6
