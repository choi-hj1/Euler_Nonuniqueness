import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

open Filter Metric
open scoped Topology

namespace EulerNonuniqueness.General

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_uniform_normalized_projection_recovery
    (base : Space) (normalize coordinate observable : Space → Space)
    (projection : Space →L[ℝ] Space) (valid : Space → Prop)
    (normalizes : ContinuousAt normalize base) (normalBase : normalize base = base)
    (coordinates : ContinuousAt coordinate base) (coordinateBase : coordinate base = 0)
    (recoveryRadius : ℝ) (recoveryPositive : 0 < recoveryRadius)
    (recoveryConstant : ℝ) (recoveryOne : 1 ≤ recoveryConstant)
    (recovery : ∀ original correction : Space,
      ‖original - base‖ + ‖correction‖ ≤ recoveryRadius → valid original →
      ‖normalize (original - correction) - original‖ ≤ recoveryConstant * ‖correction‖)
    (inverseRadius : ℝ) (inversePositive : 0 < inverseRadius)
    (inverseConstant : ℝ) (inverseOne : 1 ≤ inverseConstant)
    (inverseDifference : ∀ first second : Space,
      ‖first - base‖ ≤ inverseRadius → ‖second - base‖ ≤ inverseRadius →
      ‖coordinate first - coordinate second‖ ≤ inverseConstant * ‖first - second‖)
    (quadraticRadius : ℝ) (quadraticPositive : 0 < quadraticRadius)
    (quadraticRecovery : ∀ data : Space, ‖data‖ ≤ quadraticRadius →
      ‖projection data‖ ≤ 2 * ‖observable data‖) :
    ∃ radius > 0, ∃ constant ≥ 1, ∀ original corrected : Space,
      ‖original - base‖ + ‖original - corrected‖ ≤ radius → valid original →
      ‖projection (coordinate original)‖ ≤
        constant * (‖observable (coordinate (normalize corrected))‖ + ‖original - corrected‖) := by
  have normalLimit : Tendsto normalize (𝓝 base) (𝓝 base) := by
    simpa only [normalBase] using normalizes.tendsto
  have coordinateLimit : Tendsto (fun data => coordinate (normalize data)) (𝓝 base) (𝓝 0) := by
    have outer : Tendsto coordinate (𝓝 base) (𝓝 0) := by
      simpa only [coordinateBase] using coordinates.tendsto
    exact outer.comp normalLimit
  obtain ⟨outerRadius, outerPositive, contained⟩ := Metric.eventually_nhds_iff.mp
    ((normalLimit.eventually (Metric.ball_mem_nhds base inversePositive)).and
      (coordinateLimit.eventually (Metric.ball_mem_nhds 0 quadraticPositive)))
  let radius := min recoveryRadius (min inverseRadius (outerRadius / 2))
  let coefficient := ‖projection‖ * inverseConstant * recoveryConstant
  let constant := coefficient + 2
  have coefficientNonnegative : 0 ≤ coefficient := by dsimp [coefficient]; positivity
  refine ⟨radius, by dsimp [radius]; positivity, constant, by dsimp [constant]; linarith, ?_⟩
  intro original corrected small validOriginal
  have originalNear : ‖original - base‖ ≤ radius := by linarith [norm_nonneg (original - corrected)]
  have correctedIdentity : corrected - base = (original - base) - (original - corrected) := by abel
  have correctedNear : ‖corrected - base‖ ≤ radius := by
    rw [correctedIdentity]
    exact (norm_sub_le _ _).trans small
  obtain ⟨normalNear, coordinateNear⟩ := contained
    (show dist corrected base < outerRadius by
      rw [dist_eq_norm]
      exact (correctedNear.trans ((min_le_right _ _).trans (min_le_right _ _))).trans_lt (by linarith))
  have originalInverse : ‖original - base‖ ≤ inverseRadius :=
    originalNear.trans ((min_le_right _ _).trans (min_le_left _ _))
  have normalInverse : ‖normalize corrected - base‖ ≤ inverseRadius :=
    (show ‖normalize corrected - base‖ < inverseRadius by
      simpa only [Metric.mem_ball, dist_eq_norm] using normalNear).le
  have coordinateSmall : ‖coordinate (normalize corrected)‖ ≤ quadraticRadius :=
    (show ‖coordinate (normalize corrected)‖ < quadraticRadius by
      simpa only [Metric.mem_ball, dist_zero_right] using coordinateNear).le
  have reconstruct : original - (original - corrected) = corrected := by abel
  have recoveryBound := recovery original (original - corrected) (small.trans (min_le_left _ _)) validOriginal
  rw [reconstruct] at recoveryBound
  have inverseBound := inverseDifference original (normalize corrected) originalInverse normalInverse
  rw [norm_sub_rev original (normalize corrected)] at inverseBound
  have coordinateDifference := inverseBound.trans
    (mul_le_mul_of_nonneg_left recoveryBound (by linarith : 0 ≤ inverseConstant))
  have transverseDifference := (projection.le_opNorm
    (coordinate original - coordinate (normalize corrected))).trans
      (mul_le_mul_of_nonneg_left coordinateDifference (norm_nonneg projection))
  rw [map_sub] at transverseDifference
  have normalizedBound := quadraticRecovery _ coordinateSmall
  have triangle := norm_add_le
    (projection (coordinate original) - projection (coordinate (normalize corrected)))
    (projection (coordinate (normalize corrected)))
  rw [sub_add_cancel] at triangle
  have actual := triangle.trans (add_le_add transverseDifference normalizedBound)
  have enlarged : coefficient * ‖original - corrected‖ + 2 * ‖observable (coordinate (normalize corrected))‖ ≤
      constant * (‖observable (coordinate (normalize corrected))‖ + ‖original - corrected‖) := by
    rw [show constant = coefficient + 2 from rfl]
    nlinarith [mul_nonneg coefficientNonnegative (norm_nonneg (observable (coordinate (normalize corrected)))),
      norm_nonneg (original - corrected)]
  apply actual.trans
  convert enlarged using 1 <;> dsimp only [coefficient] <;> ring

end EulerNonuniqueness.General
