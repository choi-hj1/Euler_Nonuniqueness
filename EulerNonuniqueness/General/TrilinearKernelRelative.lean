import EulerNonuniqueness.General.TrilinearKernelDerivative

noncomputable section

namespace EulerNonuniqueness.General

variable {Space Range : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Range] [NormedSpace ℝ Range]

attribute [local instance] trilinearKernelLinearGroup trilinearKernelLinearSpace
  trilinearKernelBilinearGroup trilinearKernelBilinearSpace trilinearKernelThirdGroup trilinearKernelThirdSpace

theorem trilinearKernelDerivative_difference_norm_le
    (trilinear : Space →L[ℝ] Space →L[ℝ] Space →L[ℝ] Range)
    (kernel : Space → Space) (kernelDerivative : Space → Space →L[ℝ] Space)
    (first final : Space) {bound : ℝ} (nonnegative : 0 ≤ bound)
    (firstBound : ‖first‖ ≤ 3) (finalBound : ‖final‖ ≤ 3)
    (firstKernel : ‖kernel first‖ ≤ bound) (finalKernel : ‖kernel final‖ ≤ bound)
    (firstDerivative : ‖kernelDerivative first‖ ≤ bound) (finalDerivative : ‖kernelDerivative final‖ ≤ bound)
    (kernelDifference : ‖kernel first - kernel final‖ ≤ bound * ‖first - final‖)
    (derivativeDifference : ‖kernelDerivative first - kernelDerivative final‖ ≤ bound * ‖first - final‖) :
    ‖trilinearKernelDerivative trilinear kernel kernelDerivative first -
      trilinearKernelDerivative trilinear kernel kernelDerivative final‖ ≤
      23 * ‖trilinear‖ * bound * ‖first - final‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro direction
  have firstApplied : ‖kernelDerivative first direction‖ ≤ bound * ‖direction‖ :=
    ((kernelDerivative first).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right firstDerivative (norm_nonneg direction))
  have finalApplied : ‖kernelDerivative final direction‖ ≤ bound * ‖direction‖ :=
    ((kernelDerivative final).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right finalDerivative (norm_nonneg direction))
  have differenceApplied : ‖(kernelDerivative first - kernelDerivative final) direction‖ ≤
      (bound * ‖first - final‖) * ‖direction‖ :=
    ((kernelDerivative first - kernelDerivative final).le_opNorm direction).trans
      (mul_le_mul_of_nonneg_right derivativeDifference (norm_nonneg direction))
  have firstIdentity : trilinear direction (kernel first) first - trilinear direction (kernel final) final =
      trilinear direction (kernel first - kernel final) first +
        trilinear direction (kernel final) (first - final) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have firstTerm : ‖trilinear direction (kernel first) first - trilinear direction (kernel final) final‖ ≤
      4 * ‖trilinear‖ * bound * ‖first - final‖ * ‖direction‖ := by
    rw [firstIdentity]
    have firstPiece : ‖trilinear direction (kernel first - kernel final) first‖ ≤
        ‖trilinear‖ * ‖direction‖ * (bound * ‖first - final‖) * 3 := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    have secondPiece : ‖trilinear direction (kernel final) (first - final)‖ ≤
        ‖trilinear‖ * ‖direction‖ * bound * ‖first - final‖ := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    exact ((norm_add_le _ _).trans (add_le_add firstPiece secondPiece)).trans_eq (by ring)
  have middleIdentity : trilinear first (kernelDerivative first direction) first -
      trilinear final (kernelDerivative final direction) final =
      trilinear (first - final) (kernelDerivative first direction) first +
        trilinear final ((kernelDerivative first - kernelDerivative final) direction) first +
          trilinear final (kernelDerivative final direction) (first - final) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have middleTerm : ‖trilinear first (kernelDerivative first direction) first -
      trilinear final (kernelDerivative final direction) final‖ ≤
      15 * ‖trilinear‖ * bound * ‖first - final‖ * ‖direction‖ := by
    rw [middleIdentity]
    have firstPiece : ‖trilinear (first - final) (kernelDerivative first direction) first‖ ≤
        ‖trilinear‖ * ‖first - final‖ * (bound * ‖direction‖) * 3 := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    have secondPiece : ‖trilinear final ((kernelDerivative first - kernelDerivative final) direction) first‖ ≤
        ‖trilinear‖ * 3 * ((bound * ‖first - final‖) * ‖direction‖) * 3 := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    have thirdPiece : ‖trilinear final (kernelDerivative final direction) (first - final)‖ ≤
        ‖trilinear‖ * 3 * (bound * ‖direction‖) * ‖first - final‖ := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
      ((add_le_add (add_le_add firstPiece secondPiece) thirdPiece).trans_eq (by ring))
  have finalIdentity : trilinear first (kernel first) direction - trilinear final (kernel final) direction =
      trilinear (first - final) (kernel first) direction +
        trilinear final (kernel first - kernel final) direction := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have finalTerm : ‖trilinear first (kernel first) direction - trilinear final (kernel final) direction‖ ≤
      4 * ‖trilinear‖ * bound * ‖first - final‖ * ‖direction‖ := by
    rw [finalIdentity]
    have firstPiece : ‖trilinear (first - final) (kernel first) direction‖ ≤
        ‖trilinear‖ * ‖first - final‖ * bound * ‖direction‖ := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    have secondPiece : ‖trilinear final (kernel first - kernel final) direction‖ ≤
        ‖trilinear‖ * 3 * (bound * ‖first - final‖) * ‖direction‖ := by
      apply (norm_trilinear_apply_le _ _ _ _).trans
      gcongr
    exact ((norm_add_le _ _).trans (add_le_add firstPiece secondPiece)).trans_eq (by ring)
  have identity : (trilinearKernelDerivative trilinear kernel kernelDerivative first -
      trilinearKernelDerivative trilinear kernel kernelDerivative final) direction =
      (trilinear direction (kernel first) first - trilinear direction (kernel final) final) +
        (trilinear first (kernelDerivative first direction) first - trilinear final (kernelDerivative final direction) final) +
          (trilinear first (kernel first) direction - trilinear final (kernel final) direction) := by
    rw [ContinuousLinearMap.sub_apply, trilinearKernelDerivative_apply, trilinearKernelDerivative_apply]
    abel
  rw [identity]
  exact ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)).trans
    ((add_le_add (add_le_add firstTerm middleTerm) finalTerm).trans_eq (by ring))

end EulerNonuniqueness.General
