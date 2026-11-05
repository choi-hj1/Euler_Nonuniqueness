import EulerNonuniqueness.General.RelativeCubicTaylor

open Set Metric
open scoped NNReal

namespace EulerNonuniqueness.General

noncomputable section

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

attribute [local instance] relativeCubicBilinearGroup relativeCubicBilinearSpace

local instance incrementBilinearAddCommMonoid : AddCommMonoid (BilinearEnd Space) :=
  relativeCubicBilinearGroup.toAddCommGroup.toAddCommMonoid

theorem norm_cubic_taylor_remainder_increment_difference
    (function : Space → Space) (first : Space → Space →L[ℝ] Space)
    (second : Space → BilinearEnd Space) {radius : ℝ} (constant : ℝ≥0)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt function (first value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Space) radius,
      HasFDerivAt first (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Space) radius))
    (base initial final : Space)
    (inside : ‖base‖ + (‖initial‖ + ‖final‖) ≤ radius)
    (quadratic : BilinearEnd Space) (secondIdentity : second base = quadratic + quadratic.flip) :
    ‖(function (base + initial) - function base - first base initial - quadratic initial initial) -
      (function (base + final) - function base - first base final - quadratic final final)‖ ≤
      (constant : ℝ) * (‖initial‖ + ‖final‖) ^ 2 * ‖initial - final‖ := by
  let size := ‖initial‖ + ‖final‖
  have sizeNonnegative : 0 ≤ size := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have contained (point : Space) (member : point ∈ closedBall (0 : Space) size) :
      base + point ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le base point).trans
      ((add_le_add_left (mem_closedBall_zero_iff.mp member) ‖base‖).trans inside)
  let remainder := fun point => function (base + point) - function base -
    first base point - quadratic point point
  let derivative := fun point => first (base + point) - first base - (quadratic + quadratic.flip) point
  let derivativeSecond := fun point => second (base + point) - (quadratic + quadratic.flip)
  have remainderActual (point : Space) (member : point ∈ closedBall (0 : Space) size) :
      HasFDerivAt remainder (derivative point) point := by
    have translation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add base
    have quadraticActual := (quadratic.hasFDerivAt (x := point)).clm_apply (hasFDerivAt_id point)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id, ContinuousLinearMap.add_apply] using
      ((((actualFirst _ (contained point member)).comp point translation).sub_const
        (function base)).sub ((first base).hasFDerivAt (x := point))).sub quadraticActual
  have derivativeActual (point : Space) (member : point ∈ closedBall (0 : Space) size) :
      HasFDerivAt derivative (derivativeSecond point) point := by
    have translation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add base
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (((actualSecond _ (contained point member)).comp point translation).sub_const (first base)).sub
        ((quadratic + quadratic.flip).hasFDerivAt (x := point))
  have secondLipschitz : LipschitzOnWith constant derivativeSecond (closedBall (0 : Space) size) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro left leftInside right rightInside
    have bound := lipschitz.dist_le_mul (base + left) (contained left leftInside)
      (base + right) (contained right rightInside)
    simpa only [derivativeSecond, dist_sub_right, dist_add_left] using bound
  have derivativeBound (point : Space) (member : point ∈ closedBall (0 : Space) size) :
      ‖derivative point‖ ≤ (constant : ℝ) * ‖point‖ ^ 2 :=
    derivative_quadratic_bound_of_lipschitz_second derivative derivativeSecond sizeNonnegative constant
      derivativeActual secondLipschitz (by simp [derivative])
      (by simp [derivativeSecond, secondIdentity]) point member
  have initialInside : initial ∈ closedBall (0 : Space) size :=
    mem_closedBall_zero_iff.mpr (le_add_of_nonneg_right (norm_nonneg final))
  have finalInside : final ∈ closedBall (0 : Space) size :=
    mem_closedBall_zero_iff.mpr (le_add_of_nonneg_left (norm_nonneg initial))
  have bound := (convex_closedBall (0 : Space) size).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun point member => (remainderActual point member).hasFDerivWithinAt)
    (fun point member => (derivativeBound point member).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg point) (mem_closedBall_zero_iff.mp member) 2) constant.coe_nonneg))
    finalInside initialInside
  exact bound

end

end EulerNonuniqueness.General
