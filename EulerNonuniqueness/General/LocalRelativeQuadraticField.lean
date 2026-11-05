import EulerNonuniqueness.General.LocalFiberOperatorBounds
import EulerNonuniqueness.Section3.LocalLipschitzCalculus

namespace EulerNonuniqueness.General

noncomputable section

open Filter Metric
open scoped Topology

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem exists_relative_quadratic_field_ball
    (neutral : Space →L[ℝ] Space) (transverse : Space → Space) (coefficient : Space → BilinearEnd Space)
    (field remainder : Space → Space) (valid : Space → Prop) {factor : ℝ}
    (transverseContinuous : ContinuousAt transverse 0) (transverseZero : transverse 0 = 0)
    (factorNonnegative : 0 ≤ factor)
    (coefficientRegular : LipschitzNear coefficient (0 : Space))
    (neutralParameter : ∀ state, coefficient (neutral state) = coefficient state)
    (remainderRelative : ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖remainder initial - remainder final‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 3 * ‖neutral initial - neutral final‖))
    (fieldEstimate : ∀ initial final : Space,
      ‖field initial - field final‖ ≤ factor *
        (‖coefficient initial‖ * (‖transverse initial‖ + ‖transverse final‖) *
          ‖transverse initial - transverse final‖ +
          ‖coefficient initial - coefficient final‖ * ‖transverse final‖ ^ 2 +
          ‖remainder initial - remainder final‖)) :
    ∃ radius > 0, ∃ constant ≥ 0, ∀ initial final : Space,
      initial ∈ ball 0 radius → final ∈ ball 0 radius → valid initial → valid final →
      ‖field initial - field final‖ ≤ constant *
        ((‖transverse initial‖ + ‖transverse final‖) * ‖transverse initial - transverse final‖ +
          (‖transverse initial‖ + ‖transverse final‖) ^ 2 * ‖neutral initial - neutral final‖) := by
  obtain ⟨rawRadius, rawPositive, rawConstant, rawNonnegative, rawBound⟩ := remainderRelative
  obtain ⟨bound, boundNonnegative, bounded⟩ := exists_eventually_norm_bound
    (Space := Space) (Target := BilinearEnd Space) coefficientRegular.continuousAt
  obtain ⟨lip, domain, nearby, lipschitz⟩ := coefficientRegular
  have neutralInside : ∀ᶠ state in 𝓝 (0 : Space), neutral state ∈ domain := by
    have limit : Tendsto neutral (𝓝 (0 : Space)) (𝓝 0) := by
      simpa only [map_zero] using neutral.continuous.tendsto (0 : Space)
    exact limit.eventually nearby
  have small : ∀ᶠ state in 𝓝 (0 : Space), ‖transverse state‖ < 1 / 2 :=
    transverseContinuous.norm.eventually (gt_mem_nhds (by
      simp only [transverseZero, norm_zero]; norm_num))
  have combined : {state | state ∈ ball 0 rawRadius ∧ ‖coefficient state‖ ≤ bound ∧
      neutral state ∈ domain ∧ ‖transverse state‖ < 1 / 2} ∈ 𝓝 (0 : Space) := by
    filter_upwards [ball_mem_nhds (0 : Space) rawPositive, bounded, neutralInside, small]
      with state raw normBound inside size
    exact ⟨raw, normBound, inside, size⟩
  obtain ⟨radius, positive, contained⟩ := Metric.mem_nhds_iff.mp combined
  refine ⟨radius, positive, factor * (bound + lip + rawConstant), by positivity, ?_⟩
  intro initial final initialInside finalInside initialValid finalValid
  obtain ⟨initialRaw, initialBound, initialDomain, initialSmall⟩ := contained initialInside
  obtain ⟨finalRaw, _, finalDomain, finalSmall⟩ := contained finalInside
  have coefficientDifference : ‖coefficient initial - coefficient final‖ ≤
      lip * ‖neutral initial - neutral final‖ := by
    rw [← neutralParameter initial, ← neutralParameter final]
    exact lipschitz.norm_sub_le (f := coefficient) initialDomain finalDomain
  have raw := rawBound initial final initialRaw finalRaw initialValid finalValid
  let size := ‖transverse initial‖ + ‖transverse final‖
  have sizeNonnegative : 0 ≤ size := by dsimp only [size]; positivity
  have sizeSmall : size ≤ 1 := by dsimp only [size]; linarith
  have squareSmall : size ^ 2 ≤ size := by nlinarith
  have cubeSmall : size ^ 3 ≤ size ^ 2 := by nlinarith [mul_nonneg (sq_nonneg size) (sub_nonneg.mpr sizeSmall)]
  have finalSquare : ‖transverse final‖ ^ 2 ≤ size ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (le_add_of_nonneg_left (norm_nonneg _)) _
  apply (fieldEstimate initial final).trans
  calc
    _ ≤ factor * (bound * size * ‖transverse initial - transverse final‖ +
        (lip * ‖neutral initial - neutral final‖) * ‖transverse final‖ ^ 2 +
        rawConstant * (size ^ 2 * ‖transverse initial - transverse final‖ + size ^ 3 * ‖neutral initial - neutral final‖)) := by
      gcongr
    _ ≤ factor * (bound * size * ‖transverse initial - transverse final‖ +
        (lip * ‖neutral initial - neutral final‖) * size ^ 2 +
        rawConstant * (size * ‖transverse initial - transverse final‖ + size ^ 2 * ‖neutral initial - neutral final‖)) := by
      gcongr
    _ ≤ factor * (bound + lip + rawConstant) *
        (size * ‖transverse initial - transverse final‖ + size ^ 2 * ‖neutral initial - neutral final‖) := by
      rw [mul_assoc factor (bound + ↑lip + rawConstant)]
      apply mul_le_mul_of_nonneg_left _ factorNonnegative
      nlinarith [mul_nonneg boundNonnegative (mul_nonneg (sq_nonneg size) (norm_nonneg (neutral initial - neutral final))),
        mul_nonneg lip.coe_nonneg (mul_nonneg sizeNonnegative (norm_nonneg (transverse initial - transverse final)))]

end

end EulerNonuniqueness.General
