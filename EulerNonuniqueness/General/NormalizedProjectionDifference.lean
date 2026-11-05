import EulerNonuniqueness.General.NormalizedProjectionRecovery

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_uniform_normalized_projection_difference
    (base : Space) (normalize coordinate : Space → Space)
    (projection : Space →L[ℝ] Space) (valid : Space → Prop)
    (normalizes : ContinuousAt normalize base) (normalBase : normalize base = base)
    (recoveryRadius : ℝ) (recoveryPositive : 0 < recoveryRadius)
    (recoveryConstant : ℝ) (recoveryOne : 1 ≤ recoveryConstant)
    (recovery : ∀ original correction : Space,
      ‖original - base‖ + ‖correction‖ ≤ recoveryRadius → valid original →
      ‖normalize (original - correction) - original‖ ≤ recoveryConstant * ‖correction‖)
    (inverseRadius : ℝ) (inversePositive : 0 < inverseRadius)
    (inverseConstant : ℝ) (inverseOne : 1 ≤ inverseConstant)
    (inverseDifference : ∀ first second : Space,
      ‖first - base‖ ≤ inverseRadius → ‖second - base‖ ≤ inverseRadius →
      ‖coordinate first - coordinate second‖ ≤ inverseConstant * ‖first - second‖) :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ original corrected : Space,
      ‖original - base‖ + ‖original - corrected‖ ≤ radius → valid original →
      ‖projection (coordinate (normalize corrected)) - projection (coordinate original)‖ ≤
        constant * ‖original - corrected‖ := by
  have normalLimit : Tendsto normalize (𝓝 base) (𝓝 base) := by
    simpa only [normalBase] using normalizes.tendsto
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    (normalLimit.eventually (Metric.ball_mem_nhds base inversePositive))
  let radius := min recoveryRadius (min inverseRadius (outerRadius / 2))
  let coefficient := ‖projection‖ * inverseConstant * recoveryConstant
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  refine ⟨radius, by dsimp [radius]; positivity, coefficient + 1, by linarith, ?_⟩
  intro original corrected small validOriginal
  have originalNear : ‖original - base‖ ≤ radius := by linarith [norm_nonneg (original - corrected)]
  have correctedIdentity : corrected - base = (original - base) - (original - corrected) := by abel
  have correctedNear : ‖corrected - base‖ ≤ radius := by
    rw [correctedIdentity]
    exact (norm_sub_le _ _).trans small
  have normalNear := contained (show dist corrected base < outerRadius by
    rw [dist_eq_norm]
    exact (correctedNear.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith))
  have originalInverse : ‖original - base‖ ≤ inverseRadius :=
    originalNear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have normalInverse : ‖normalize corrected - base‖ ≤ inverseRadius :=
    (show ‖normalize corrected - base‖ < inverseRadius by
      simpa only [Metric.mem_ball, dist_eq_norm] using normalNear).le
  have reconstruct : original - (original - corrected) = corrected := by abel
  have recoveryBound := recovery original (original - corrected) (small.trans (min_le_left _ _)) validOriginal
  rw [reconstruct] at recoveryBound
  have inverseBound := inverseDifference (normalize corrected) original normalInverse originalInverse
  have coordinateDifference := inverseBound.trans
    (mul_le_mul_of_nonneg_left recoveryBound (by linarith : 0 ≤ inverseConstant))
  have transverseDifference := (projection.le_opNorm
    (coordinate (normalize corrected) - coordinate original)).trans
      (mul_le_mul_of_nonneg_left coordinateDifference (norm_nonneg projection))
  rw [map_sub] at transverseDifference
  have scalar : ‖projection‖ * (inverseConstant * (recoveryConstant * ‖original - corrected‖)) ≤
      (coefficient + 1) * ‖original - corrected‖ := by
    dsimp only [coefficient]
    nlinarith [norm_nonneg (original - corrected)]
  exact transverseDifference.trans scalar

end EulerNonuniqueness.General
