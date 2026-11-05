import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section

open Set Metric
open scoped NNReal InnerProductSpace

namespace EulerNonuniqueness

def closedBallProjection {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] (radius : ℝ) (nonnegative : 0 ≤ radius) (point : Space) : Space :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex
    (show (closedBall (0 : Space) radius).Nonempty from ⟨0, mem_closedBall_self nonnegative⟩)
    isClosed_closedBall.isComplete (convex_closedBall (0 : Space) radius) point)

theorem closedBallProjection_spec {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] (radius : ℝ) (nonnegative : 0 ≤ radius) (point : Space) :
    closedBallProjection radius nonnegative point ∈ closedBall (0 : Space) radius ∧
      ∀ other ∈ closedBall (0 : Space) radius,
        ⟪point - closedBallProjection radius nonnegative point, other - closedBallProjection radius nonnegative point⟫_ℝ ≤ 0 := by
  have specification := Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    (show (closedBall (0 : Space) radius).Nonempty from ⟨0, mem_closedBall_self nonnegative⟩)
    isClosed_closedBall.isComplete (convex_closedBall (0 : Space) radius) point)
  exact ⟨specification.1, (norm_eq_iInf_iff_real_inner_le_zero (convex_closedBall (0 : Space) radius) specification.1).mp specification.2⟩

theorem closedBallProjection_eq_self {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] {radius : ℝ} (nonnegative : 0 ≤ radius) {point : Space}
    (inside : point ∈ closedBall (0 : Space) radius) : closedBallProjection radius nonnegative point = point := by
  have inequality := (closedBallProjection_spec radius nonnegative point).2 point inside
  rw [real_inner_self_eq_norm_sq] at inequality
  have equality : ‖point - closedBallProjection radius nonnegative point‖ = 0 := by nlinarith [norm_nonneg (point - closedBallProjection radius nonnegative point)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp equality)).symm

theorem lipschitz_closedBallProjection {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] (radius : ℝ) (nonnegative : 0 ≤ radius) :
    LipschitzWith 1 (closedBallProjection (Space := Space) radius nonnegative) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  let firstProjection := closedBallProjection radius nonnegative first
  let secondProjection := closedBallProjection radius nonnegative second
  have firstVariation := (closedBallProjection_spec radius nonnegative first).2 secondProjection
    (closedBallProjection_spec radius nonnegative second).1
  have secondVariation := (closedBallProjection_spec radius nonnegative second).2 firstProjection
    (closedBallProjection_spec radius nonnegative first).1
  have monotone : ‖firstProjection - secondProjection‖ ^ 2 ≤ ⟪first - second, firstProjection - secondProjection⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪first - firstProjection, secondProjection - firstProjection⟫_ℝ ≤ 0 at firstVariation
    change ⟪second - secondProjection, firstProjection - secondProjection⟫_ℝ ≤ 0 at secondVariation
    simp only [inner_sub_left, inner_sub_right] at firstVariation secondVariation ⊢
    linarith only [firstVariation, secondVariation, real_inner_comm firstProjection secondProjection]
  have cauchy := real_inner_le_norm (first - second) (firstProjection - secondProjection)
  have bound : ‖firstProjection - secondProjection‖ ≤ ‖first - second‖ := by
    nlinarith [norm_nonneg (firstProjection - secondProjection), norm_nonneg (first - second)]
  simpa only [dist_eq_norm, NNReal.coe_one, one_mul] using bound

theorem norm_closedBallProjection_le {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
    [CompleteSpace Space] (radius : ℝ) (nonnegative : 0 ≤ radius) (point : Space) :
    ‖closedBallProjection radius nonnegative point‖ ≤ ‖point‖ := by
  have zero : closedBallProjection radius nonnegative (0 : Space) = 0 :=
    closedBallProjection_eq_self nonnegative (mem_closedBall_self nonnegative)
  have estimate := (lipschitz_closedBallProjection (Space := Space) radius nonnegative).dist_le_mul point 0
  simpa only [zero, dist_zero_right, NNReal.coe_one, one_mul] using estimate

end EulerNonuniqueness
