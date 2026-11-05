import EulerNonuniqueness.General.QuadraticJetRemainderFactor

namespace EulerNonuniqueness.General

noncomputable section

open Set Metric
open scoped NNReal

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem norm_cubic_remainder_of_lipschitz_second
    (function : Space → Space) (derivative : Space → Space →L[ℝ] Space)
    (second : Space → BilinearEnd Space) {radius : ℝ} (constant : ℝ≥0)
    (actualFirst : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt function (derivative value) value)
    (actualSecond : ∀ value ∈ closedBall (0 : Space) radius, HasFDerivAt derivative (second value) value)
    (lipschitz : LipschitzOnWith constant second (closedBall (0 : Space) radius))
    (base increment : Space) (inside : ‖base‖ + ‖increment‖ ≤ radius)
    (bilinear : BilinearEnd Space) (secondIdentity : second base = bilinear + bilinear.flip) :
    ‖function (base + increment) - function base - derivative base increment - bilinear increment increment‖ ≤
      (constant : ℝ) * ‖increment‖ ^ 3 := by
  have contained (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      base + point ∈ closedBall (0 : Space) radius := by
    apply mem_closedBall_zero_iff.mpr
    exact (norm_add_le base point).trans
      ((add_le_add_left (mem_closedBall_zero_iff.mp member) ‖base‖).trans inside)
  let shifted := fun point => function (base + point) - function base
  let shiftedDerivative := fun point => derivative (base + point)
  let shiftedSecond := fun point => second (base + point)
  have firstActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt shifted (shiftedDerivative point) point := by
    have translation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add base
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      ((actualFirst _ (contained point member)).comp point translation).sub_const (function base)
  have secondActual (point : Space) (member : point ∈ closedBall (0 : Space) ‖increment‖) :
      HasFDerivAt shiftedDerivative (shiftedSecond point) point := by
    have translation := (hasFDerivAt_id (𝕜 := ℝ) point).const_add base
    simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using
      (actualSecond _ (contained point member)).comp point translation
  have shiftedLipschitz : LipschitzOnWith constant shiftedSecond (closedBall (0 : Space) ‖increment‖) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first firstInside secondPoint secondInside
    have bound := lipschitz.dist_le_mul (base + first) (contained first firstInside)
      (base + secondPoint) (contained secondPoint secondInside)
    simpa only [dist_add_left] using bound
  have actual := quadratic_jet_remainder_transverse_factor shifted shiftedDerivative shiftedSecond
    (derivative base) bilinear (norm_nonneg increment) constant firstActual secondActual shiftedLipschitz
    (by simp [shiftedDerivative]) (by simpa [shiftedSecond] using secondIdentity)
    (0 : Space) increment (by simp) (by simp [shifted]) (by simp) (by simp)
  simpa only [shifted, zero_add, norm_zero, zero_add, pow_succ, mul_assoc] using actual

end

end EulerNonuniqueness.General
