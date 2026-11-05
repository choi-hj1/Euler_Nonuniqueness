import EulerNonuniqueness.General.BilinearOperatorCalculus

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

set_option maxHeartbeats 1000000

theorem norm_bilinear_mean_error_difference_le
    (initial final : BilinearEnd Space) (first second radial : Space) (initialMean finalMean : ℝ) :
    ‖(initial (first + initialMean • radial) (first + initialMean • radial) - initial first first) -
      (final (second + finalMean • radial) (second + finalMean • radial) - final second second)‖ ≤
      |initialMean - finalMean| * (2 * ‖initial‖ * ‖radial‖ * ‖first‖) +
      |finalMean| * (2 * ‖initial‖ * ‖radial‖ * ‖first - second‖ +
        2 * ‖initial - final‖ * ‖radial‖ * ‖second‖) +
      (|initialMean| + |finalMean|) * |initialMean - finalMean| * (‖initial‖ * ‖radial‖ ^ 2) +
      |finalMean| ^ 2 * (‖initial - final‖ * ‖radial‖ ^ 2) := by
  have bound (bilinear : BilinearEnd Space) (left right : Space) :
      ‖bilinear left right‖ ≤ ‖bilinear‖ * ‖left‖ * ‖right‖ :=
    ((bilinear left).le_opNorm right).trans
      (mul_le_mul_of_nonneg_right (bilinear.le_opNorm left) (norm_nonneg right))
  let firstCross := initial radial first + initial first radial
  let finalCross := final radial second + final second radial
  have firstCrossBound : ‖firstCross‖ ≤ 2 * ‖initial‖ * ‖radial‖ * ‖first‖ := by
    exact ((norm_add_le _ _).trans (add_le_add (bound _ _ _) (bound _ _ _))).trans_eq (by ring)
  have firstDifference : initial radial first - final radial second =
      initial radial (first - second) + (initial - final) radial second := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have secondDifference : initial first radial - final second radial =
      initial (first - second) radial + (initial - final) second radial := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  have crossIdentity : firstCross - finalCross =
      (initial radial first - final radial second) + (initial first radial - final second radial) := by
    dsimp only [firstCross, finalCross]
    abel
  have crossDifference : ‖firstCross - finalCross‖ ≤
      2 * ‖initial‖ * ‖radial‖ * ‖first - second‖ + 2 * ‖initial - final‖ * ‖radial‖ * ‖second‖ := by
    rw [crossIdentity, firstDifference, secondDifference]
    apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))).trans
    exact (add_le_add (add_le_add (bound _ _ _) (bound _ _ _))
      (add_le_add (bound _ _ _) (bound _ _ _))).trans_eq (by ring)
  have squareDifference : |initialMean ^ 2 - finalMean ^ 2| ≤
      (|initialMean| + |finalMean|) * |initialMean - finalMean| := by
    rw [show initialMean ^ 2 - finalMean ^ 2 = (initialMean + finalMean) * (initialMean - finalMean) by ring, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_add _ _) (abs_nonneg _)
  have expansion (bilinear : BilinearEnd Space) (vector : Space) (mean : ℝ) :
      bilinear (vector + mean • radial) (vector + mean • radial) - bilinear vector vector =
        mean • (bilinear radial vector + bilinear vector radial) + mean ^ 2 • bilinear radial radial := by
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
    module
  have identity :
      (initial (first + initialMean • radial) (first + initialMean • radial) - initial first first) -
        (final (second + finalMean • radial) (second + finalMean • radial) - final second second) =
      (initialMean - finalMean) • firstCross + finalMean • (firstCross - finalCross) +
        (initialMean ^ 2 - finalMean ^ 2) • initial radial radial +
          finalMean ^ 2 • (initial - final) radial radial := by
    rw [expansion, expansion]
    dsimp only [firstCross, finalCross]
    simp only [ContinuousLinearMap.sub_apply]
    module
  rw [identity]
  apply ((norm_add_le _ _).trans (add_le_add_right
    ((norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)) _)).trans
  simp only [norm_smul, Real.norm_eq_abs, abs_pow]
  exact add_le_add (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left firstCrossBound (abs_nonneg _))
      (mul_le_mul_of_nonneg_left crossDifference (abs_nonneg _)))
    (mul_le_mul squareDifference ((bound initial radial radial).trans_eq (by ring))
      (norm_nonneg _) (by positivity)))
    (mul_le_mul_of_nonneg_left ((bound (initial - final) radial radial).trans_eq (by ring)) (sq_nonneg _))

end

end EulerNonuniqueness.General
